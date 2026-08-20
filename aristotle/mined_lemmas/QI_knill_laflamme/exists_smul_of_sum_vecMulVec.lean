/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]

/-- A *code* is given by the orthogonal projection `P` onto the code subspace: `P` is
self-adjoint, idempotent, and nonzero (the code subspace is nontrivial). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  nontrivial : P ≠ 0

/-- The error set `E` is the Kraus family of a quantum channel (trace preserving). -/

lemma exists_smul_of_sum_vecMulVec {ι : Type*} [Fintype ι] (w : ι → n → ℂ) (psi : n → ℂ)
    (h : ∑ i, vecMulVec (w i) (star (w i)) = vecMulVec psi (star psi)) (i : ι) :
    ∃ mu : ℂ, w i = mu • psi := by
  have key : ∀ v : n → ℂ, ∑ j, (star (w j) ⬝ᵥ v) * (star v ⬝ᵥ w j)
      = (star psi ⬝ᵥ v) * (star v ⬝ᵥ psi) := by
    intro v
    have := congrArg (fun M : Matrix n n ℂ => star v ⬝ᵥ (M *ᵥ v)) h
    simpa only [Matrix.sum_mulVec, dotProduct_sum, vecMulVec_mulVec, dotProduct_smul,
      smul_eq_mul] using this
  set N : ℂ := star psi ⬝ᵥ psi with hN
  set mu : ℂ := (star psi ⬝ᵥ w i) / N with hmu
  refine ⟨mu, ?_⟩
  set v : n → ℂ := w i - mu • psi with hv
  have hstarv : star v = star (w i) - (starRingEnd ℂ mu) • star psi := by
    simp [hv, star_sub, star_smul]
  have hNconj : (starRingEnd ℂ) N = N := by
    simpa [hN] using conj_dotProduct_star psi psi
  have hvpsi : star v ⬝ᵥ psi = 0 := by
    rw [hstarv, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rcases eq_or_ne psi 0 with hp | hp
    · simp [hp]
    · have hNne : N ≠ 0 := by
        rw [hN]
        exact fun hc => hp (dotProduct_star_self_eq_zero.1 (by simpa using hc))
      have h2 : (starRingEnd ℂ) mu * N = star (w i) ⬝ᵥ psi := by
        rw [hmu, map_div₀, hNconj, conj_dotProduct_star]
        field_simp
      rw [h2, sub_self]
  have hpsiv : star psi ⬝ᵥ v = 0 := by
    have := conj_dotProduct_star v psi
    rw [hvpsi] at this
    simpa using this.symm
  have hsum := key v
  rw [hpsiv, zero_mul] at hsum
  have hzero : ∀ j, star (w j) ⬝ᵥ v = 0 := by
    have hre : ∑ j, ((Complex.normSq (star (w j) ⬝ᵥ v) : ℝ) : ℂ) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← conj_dotProduct_star (w j) v, Complex.mul_conj]
    have hre' : ∑ j, Complex.normSq (star (w j) ⬝ᵥ v) = 0 := by exact_mod_cast hre
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hre' j
      (Finset.mem_univ j)
    simpa using Complex.normSq_eq_zero.1 this
  have hvv : star v ⬝ᵥ v = 0 := by
    rw [hstarv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hzero i, hpsiv]
    ring
  have hv0 := dotProduct_star_self_eq_zero.1 hvv
  rw [hv] at hv0
  linear_combination (norm := module) hv0

/-- A projector applied to any vector gives a vector of the code. -/

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

lemma exists_const_eigenvalue {P B : Matrix n n ℂ} (hP : IsCodeProjector P)
    (h : ∀ x : n → ℂ, P *ᵥ x = x → ∃ mu : ℂ, B *ᵥ x = mu • x) :
    ∃ lam : ℂ, B * P = lam • P := by
  obtain ⟨p0, hp0, hp0ne⟩ := exists_ne_zero_mem_code hP
  obtain ⟨lam, hlam⟩ := h p0 hp0
  refine ⟨lam, ?_⟩
  have main : ∀ y : n → ℂ, P *ᵥ y = y → B *ᵥ y = lam • y := by
    intro y hy
    obtain ⟨mu, hmu⟩ := h y hy
    obtain ⟨nu, hnu⟩ := h (p0 + y) (by rw [mulVec_add, hp0, hy])
    rw [mulVec_add, hlam, hmu, smul_add] at hnu
    have hkey : (lam - nu) • p0 = (nu - mu) • y := by
      linear_combination (norm := module) hnu
    rcases eq_or_ne lam nu with hln | hln
    · rw [hln, sub_self, zero_smul] at hkey
      rcases smul_eq_zero.1 hkey.symm with h1 | h1
      · rw [hmu, ← sub_eq_zero.1 h1, hln]
      · simp [h1]
    · have hne' : lam - nu ≠ 0 := sub_ne_zero.2 hln
      set t : ℂ := (nu - mu) / (lam - nu) with ht
      have hp0eq : p0 = t • y := by
        have h3 := congrArg (fun z : n → ℂ => (lam - nu)⁻¹ • z) hkey
        simp only [smul_smul, inv_mul_cancel₀ hne', one_smul] at h3
        rw [h3, ht]
        congr 1
        field_simp
      have hy0 : y ≠ 0 := by
        intro hc; rw [hc, smul_zero] at hp0eq; exact hp0ne hp0eq
      have htne : t ≠ 0 := by
        intro hc; rw [hc, zero_smul] at hp0eq; exact hp0ne hp0eq
      have h4 : (t * mu) • y = (lam * t) • y := by
        have h1 : B *ᵥ p0 = (t * mu) • y := by rw [hp0eq, mulVec_smul, hmu, smul_smul]
        have h2 : B *ᵥ p0 = (lam * t) • y := by rw [hlam, hp0eq, smul_smul]
        rw [← h1, h2]
      have h5 : (t * mu - lam * t) • y = 0 := by rw [sub_smul, h4, sub_self]
      rcases smul_eq_zero.1 h5 with h1 | h1
      · have h6 : t * (mu - lam) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 h6 with h2 | h2
        · exact absurd h2 htne
        · rw [hmu, sub_eq_zero.1 h2]
      · exact absurd h1 hy0
  ext i j
  have h7 := main (P *ᵥ Pi.single j 1) (by rw [mulVec_mulVec, hP.idem])
  rw [mulVec_mulVec] at h7
  have hcol := congrFun h7 i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hcol

/-! ### The forward direction: correctability implies the Knill–Laflamme conditions -/

omit [DecidableEq A] in

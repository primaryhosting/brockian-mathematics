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

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

lemma hasScalarRecovery_of_corrects (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : CorrectsErrorSet P E) : HasScalarRecovery P E := by
  obtain ⟨m, R, hsum, hc⟩ := h
  refine ⟨m, R, hsum, fun a k => ?_⟩
  obtain ⟨c, hcc⟩ := hc a
  have hmul : ∀ (A : Matrix n n ℂ) (u : n → ℂ),
      A * vecMulVec u (star u) * Aᴴ = vecMulVec (A *ᵥ u) (star (A *ᵥ u)) := by
    intro A u
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
  have key : ∀ v : n → ℂ, ∃ μ : ℂ, (R k * E a) *ᵥ (P *ᵥ v) = μ • (P *ᵥ v) := by
    intro v
    refine exists_smul_of_orthogonal _ _ ?_
    intro z hz
    set u : n → ℂ := P *ᵥ v with hu
    have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hP.idem]
    have hstaru : star u ᵥ* P = star u := by
      have h7 : star (P *ᵥ u) = star u ᵥ* Pᴴ := star_mulVec P u
      rw [hPu, hP.herm] at h7
      exact h7.symm
    have hρ : P * vecMulVec u (star u) * P = vecMulVec u (star u) := by
      rw [mul_vecMulVec, vecMulVec_mul, hPu, hstaru]
    have heq := hcc (vecMulVec u (star u)) hρ
    have hrw : ∀ j : Fin m, R j * (E a * vecMulVec u (star u) * (E a)ᴴ) * (R j)ᴴ
        = vecMulVec ((R j * E a) *ᵥ u) (star ((R j * E a) *ᵥ u)) := by
      intro j
      have h8 : R j * (E a * vecMulVec u (star u) * (E a)ᴴ) * (R j)ᴴ
          = (R j * E a) * vecMulVec u (star u) * (R j * E a)ᴴ := by
        rw [conjTranspose_mul]; noncomm_ring
      rw [h8, hmul]
    rw [Finset.sum_congr rfl fun j _ => hrw j] at heq
    have h2 := congrArg (fun M : Matrix n n ℂ => star z ⬝ᵥ (M *ᵥ z)) heq
    simp only [sum_mulVec, vecMulVec_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, hz, zero_mul, mul_zero] at h2
    have hnorm : ∀ j : Fin m, (star ((R j * E a) *ᵥ u) ⬝ᵥ z) * (star z ⬝ᵥ ((R j * E a) *ᵥ u))
        = ((Complex.normSq (star ((R j * E a) *ᵥ u) ⬝ᵥ z) : ℝ) : ℂ) := by
      intro j
      have h9 : star z ⬝ᵥ ((R j * E a) *ᵥ u)
          = (starRingEnd ℂ) (star ((R j * E a) *ᵥ u) ⬝ᵥ z) := by
        simp [dotProduct, map_sum, mul_comm]
      rw [h9, Complex.mul_conj]
    rw [Finset.sum_congr rfl fun j _ => hnorm j] at h2
    have h3 : ∑ j : Fin m, Complex.normSq (star ((R j * E a) *ᵥ u) ⬝ᵥ z) = 0 := by
      exact_mod_cast h2
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (star ((R j * E a) *ᵥ u) ⬝ᵥ z))).mp h3 k
      (Finset.mem_univ k)
    exact Complex.normSq_eq_zero.mp h4
  have h5 := exists_smul_eq_of_forall_mulVec P (R k * E a) key
  obtain ⟨l, hl⟩ := h5
  exact ⟨l, by rw [← hl]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A scalar recovery forces the Knill–Laflamme conditions. -/

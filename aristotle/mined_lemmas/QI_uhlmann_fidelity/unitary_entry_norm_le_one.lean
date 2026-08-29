import Mathlib
/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Singular value decomposition -/

/-- Every square complex matrix admits a singular value decomposition
`M = U * diagonal s * V` with `U`, `V` unitary and `s` a nonnegative real vector. -/

lemma unitary_entry_norm_le_one {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) (i j : n) :
    ‖W i j‖ ≤ 1 := by
  have hWW : Wᴴ * W = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hW
  have h0 : ∑ k, Wᴴ j k * W k j = (1 : Matrix n n ℂ) j j := by
    rw [← Matrix.mul_apply, hWW]
  rw [Matrix.one_apply_eq] at h0
  have h1 : ((∑ k, ‖W k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h0]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  have h2 : (∑ k, ‖W k j‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h1
  have h3 : ‖W i j‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖W k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (W i j)]

/-- Polar-type factorization: if `A * Aᴴ = ρ` then `A = √ρ * V` for some unitary `V`. -/

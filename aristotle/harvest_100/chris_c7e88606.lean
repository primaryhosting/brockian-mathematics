/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The 3×3 sine-kernel Hankel matrix of moments. -/
def hankelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `hankelM`. -/
def hankelMinv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

lemma hankelM_det : hankelM.det = 5/108 := by
  simp [hankelM, Matrix.det_fin_three]
  norm_num

lemma hankelM_mul_inv : hankelM * hankelMinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hankelM, hankelMinv, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> norm_num

lemma hankelM_inv_eq : hankelM⁻¹ = hankelMinv :=
  Matrix.inv_eq_right_inv hankelM_mul_inv

/--
**Christoffel inverse form.**  The sine-kernel Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` has determinant `5/108 ≠ 0`, hence is
invertible, and `(M⁻¹) 0 0 = 36/5`.  Consequently the classical Christoffel value
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio definition of `Λ₂(0;1)`.
-/
theorem christoffel_inverse_form :
    hankelM.det = 5/108 ∧ IsUnit hankelM.det ∧ hankelM⁻¹ 0 0 = 36/5 ∧
      (∑ i, ∑ j, (if i = 0 then (1:ℚ) else 0) * hankelM⁻¹ i j * (if j = 0 then (1:ℚ) else 0))⁻¹
        = 5/36 := by
  refine ⟨hankelM_det, ?_, ?_, ?_⟩
  · rw [hankelM_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [hankelM_inv_eq]; simp [hankelMinv]
  · rw [hankelM_inv_eq]
    simp [Fin.sum_univ_succ, hankelMinv]
    norm_num

end Zeta23Scaffold


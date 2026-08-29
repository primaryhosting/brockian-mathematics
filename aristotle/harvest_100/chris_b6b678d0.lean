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

/-- The `3 × 3` Hankel matrix of moments of the sine kernel. -/
def christoffelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `christoffelM`. -/
def christoffelMinv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

/-- The determinant of the Hankel matrix is `5/108`. -/
theorem christoffel_det : christoffelM.det = 5/108 := by
  simp [christoffelM, Matrix.det_fin_three]
  norm_num

/-- `christoffelMinv` is a right inverse of `christoffelM`. -/
theorem christoffel_mul_inv : christoffelM * christoffelMinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [christoffelM, christoffelMinv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The Hankel matrix is invertible. -/
theorem christoffel_isUnit : IsUnit christoffelM.det := by
  rw [christoffel_det]
  exact (isUnit_iff_ne_zero).2 (by norm_num)

/-- The inverse of the Hankel matrix is `christoffelMinv`. -/
theorem christoffel_inv_eq : christoffelM⁻¹ = christoffelMinv :=
  Matrix.inv_eq_right_inv christoffel_mul_inv

/--
Inverse-matrix cross-check for the Christoffel function: for the sine-kernel Hankel
matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]`, the matrix `M` is invertible
(its determinant is `5/108 ≠ 0`) and `(M⁻¹) 0 0 = 36/5`.  Consequently
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio (Hankel-ratio) value of
`Λ₂(0;1)`.
-/
theorem christoffel_inverse_form :
    christoffelM.det = 5/108 ∧ christoffelM.det ≠ 0 ∧
      christoffelM⁻¹ 0 0 = 36/5 ∧ (christoffelM⁻¹ 0 0)⁻¹ = 5/36 := by
  refine ⟨christoffel_det, ?_, ?_, ?_⟩
  · rw [christoffel_det]; norm_num
  · rw [christoffel_inv_eq]; simp [christoffelMinv]
  · rw [christoffel_inv_eq]; norm_num [christoffelMinv]

end Zeta23Scaffold


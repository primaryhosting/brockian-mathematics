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

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The `3 × 3` sine-kernel Hankel matrix. -/
def christoffelHankelMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `christoffelHankelMatrix`. -/
def christoffelHankelInv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

theorem christoffelHankelMatrix_det :
    christoffelHankelMatrix.det = 5/108 := by
  simp [christoffelHankelMatrix, Matrix.det_fin_three]
  norm_num

theorem christoffelHankelMatrix_mul_inv :
    christoffelHankelMatrix * christoffelHankelInv = 1 := by
  simp [christoffelHankelMatrix, christoffelHankelInv, Matrix.one_fin_three]
  norm_num

/-- Inverse-matrix cross-check for the Christoffel function: the sine-kernel Hankel
matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` is invertible (its determinant is
`5/108 ≠ 0`) and `(M⁻¹) 0 0 = 36/5`, so `1 / (eᵀ₀ M⁻¹ e₀) = 5/36`, agreeing with the
determinant-ratio (Hankel) value of `Λ₂(0;1)`. -/
theorem christoffel_inverse_form :
    christoffelHankelMatrix.det = 5/108 ∧
      IsUnit christoffelHankelMatrix.det ∧
      christoffelHankelMatrix⁻¹ 0 0 = 36/5 ∧
      1 / (Pi.single (0 : Fin 3) (1 : ℚ) ⬝ᵥ
            christoffelHankelMatrix⁻¹.mulVec (Pi.single (0 : Fin 3) (1 : ℚ))) = 5/36 := by
  have hdet : christoffelHankelMatrix.det = 5/108 := christoffelHankelMatrix_det
  have hunit : IsUnit christoffelHankelMatrix.det := by
    rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hinv : christoffelHankelMatrix⁻¹ = christoffelHankelInv :=
    Matrix.inv_eq_right_inv christoffelHankelMatrix_mul_inv
  refine ⟨hdet, hunit, ?_, ?_⟩
  · rw [hinv, christoffelHankelInv]
    norm_num
  · rw [hinv, christoffelHankelInv]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

end Zeta23Scaffold

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


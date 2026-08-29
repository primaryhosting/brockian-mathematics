/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

/-- The order-3 sine-kernel Hankel matrix. -/
def christoffelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The determinant of the sine-kernel Hankel matrix is `5/108`. -/
theorem christoffelM_det : christoffelM.det = 5 / 108 := by
  simp [christoffelM, Matrix.det_fin_three]
  norm_num

/-- The Hankel matrix is invertible. -/
theorem christoffelM_isUnit_det : IsUnit christoffelM.det := by
  rw [christoffelM_det]
  exact isUnit_iff_ne_zero.2 (by norm_num)

/-- The `(0,0)` entry of the inverse Hankel matrix is `36/5`. -/
theorem christoffelM_inv_zero_zero : christoffelM⁻¹ 0 0 = 36 / 5 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_three, christoffelM_det]
  simp [christoffelM]
  norm_num

/-- **Christoffel inverse form.** The sine-kernel Hankel matrix `M` is invertible
(its determinant is `5/108 ≠ 0`), the `(0,0)` entry of `M⁻¹` is `36/5`, and hence the
classical Christoffel value `1 / (e₀ᵀ M⁻¹ e₀)` equals `5/36`, matching the
determinant-ratio definition of `Λ₂(0;1)`. -/
theorem christoffel_inverse_form :
    IsUnit christoffelM.det ∧ christoffelM⁻¹ 0 0 = 36 / 5 ∧
      (Pi.single 0 (1 : ℚ)) ⬝ᵥ (christoffelM⁻¹ *ᵥ (Pi.single 0 (1 : ℚ))) = 36 / 5 ∧
      1 / ((Pi.single 0 (1 : ℚ)) ⬝ᵥ (christoffelM⁻¹ *ᵥ (Pi.single 0 (1 : ℚ)))) = 5 / 36 := by
  have hquad : (Pi.single 0 (1 : ℚ)) ⬝ᵥ (christoffelM⁻¹ *ᵥ (Pi.single 0 (1 : ℚ)))
      = christoffelM⁻¹ 0 0 := by
    simp [single_dotProduct, Matrix.mulVec_single]
  refine ⟨christoffelM_isUnit_det, christoffelM_inv_zero_zero, ?_, ?_⟩
  · rw [hquad, christoffelM_inv_zero_zero]
  · rw [hquad, christoffelM_inv_zero_zero]
    norm_num

end Zeta23Scaffold


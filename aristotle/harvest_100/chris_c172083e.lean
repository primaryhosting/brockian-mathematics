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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Scaffold

/-- The `3 × 3` sine-kernel Hankel moment matrix. -/
def sineHankelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The determinant of the sine-kernel Hankel matrix is `5/108`. -/
theorem sineHankelM_det : sineHankelM.det = 5 / 108 := by
  simp [sineHankelM, Matrix.det_fin_three]
  norm_num

/-- The sine-kernel Hankel matrix is invertible. -/
theorem sineHankelM_isUnit_det : IsUnit sineHankelM.det := by
  rw [sineHankelM_det]
  exact (isUnit_iff_ne_zero).2 (by norm_num)

/-- The `(0,0)` entry of the inverse of the sine-kernel Hankel matrix is `36/5`. -/
theorem sineHankelM_inv_zero_zero : sineHankelM⁻¹ 0 0 = 36 / 5 := by
  rw [Matrix.inv_def]
  simp [sineHankelM, Matrix.det_fin_three, Matrix.adjugate_fin_three]
  norm_num

/-- The first standard basis vector `e₀ : Fin 3 → ℚ`. -/
def e0 : Fin 3 → ℚ := Pi.single 0 1

/--
**Christoffel inverse form.**

The sine-kernel Hankel matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` is invertible
(its determinant is `5/108 ≠ 0`), and the `(0,0)` entry of its inverse equals `36/5`.
Equivalently `e₀ᵀ M⁻¹ e₀ = 36/5`, so the classical Christoffel value
`1 / (e₀ᵀ M⁻¹ e₀)` equals `5/36`, agreeing with the determinant-ratio (Hankel-ratio)
value of `Λ₂(0;1)`.
-/
theorem christoffel_inverse_form :
    sineHankelM.det = 5 / 108 ∧ IsUnit sineHankelM.det ∧
      sineHankelM⁻¹ 0 0 = 36 / 5 ∧
      e0 ⬝ᵥ (sineHankelM⁻¹).mulVec e0 = 36 / 5 ∧
      (e0 ⬝ᵥ (sineHankelM⁻¹).mulVec e0)⁻¹ = 5 / 36 := by
  have h : e0 ⬝ᵥ (sineHankelM⁻¹).mulVec e0 = 36 / 5 := by
    simp [e0, Matrix.mulVec_single, sineHankelM_inv_zero_zero]
  exact ⟨sineHankelM_det, sineHankelM_isUnit_det, sineHankelM_inv_zero_zero, h, by
    rw [h]; norm_num⟩

end Zeta23Scaffold


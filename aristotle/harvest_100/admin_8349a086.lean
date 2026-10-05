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

set_option grind.warning false

namespace Zeta23Scaffold

/-- The `3 × 3` Hankel moment matrix of the sine kernel (rational entries). -/
def sineHankel3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `sineHankel3`. -/
def sineHankel3Inv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

lemma sineHankel3_det : sineHankel3.det = 5/108 := by
  simp [sineHankel3, Matrix.det_fin_three]
  norm_num

lemma sineHankel3_mul_inv : sineHankel3 * sineHankel3Inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sineHankel3, sineHankel3Inv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma sineHankel3_inv_eq : sineHankel3⁻¹ = sineHankel3Inv :=
  Matrix.inv_eq_right_inv sineHankel3_mul_inv

/--
**Christoffel inverse form.**  For the `3 × 3` sine-kernel Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` over `ℚ`, the determinant is `5/108`
(hence `M` is invertible), the `(0,0)` entry of `M⁻¹` equals `36/5`, and therefore
the classical Christoffel value `1 / (eᵀ₀ M⁻¹ e₀)` equals `5/36`, matching the
determinant-ratio definition of `Λ₂(0;1)`.
-/
theorem christoffel_inverse_form :
    sineHankel3.det = 5/108 ∧ IsUnit sineHankel3.det ∧
      sineHankel3⁻¹ 0 0 = 36/5 ∧
      (1 : ℚ) / (_root_.dotProduct (Pi.single (0 : Fin 3) (1 : ℚ))
          (Matrix.mulVec sineHankel3⁻¹ (Pi.single (0 : Fin 3) (1 : ℚ)))) = 5/36 := by
  refine ⟨sineHankel3_det, ?_, ?_, ?_⟩
  · rw [sineHankel3_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [sineHankel3_inv_eq]; simp [sineHankel3Inv]
  · rw [sineHankel3_inv_eq]
    simp [dotProduct, Matrix.mulVec, sineHankel3Inv, Pi.single_apply]

end Zeta23Scaffold


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

/-- The `3 × 3` Hankel moment matrix of the sine kernel used in the Christoffel-function
computation. -/
def sineHankel3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- **Christoffel inverse form.**  For the sine-kernel Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` we have `det M = 5/108 ≠ 0`, so `M` is invertible,
and the `(0,0)` entry of `M⁻¹` equals `36/5`.  Consequently the classical Christoffel value
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio definition of `Λ₂(0;1)`. -/
theorem christoffel_inverse_form :
    sineHankel3.det = 5/108 ∧ IsUnit sineHankel3.det ∧
      sineHankel3⁻¹ 0 0 = 36/5 ∧
      (dotProduct (Pi.single 0 1) (Matrix.mulVec sineHankel3⁻¹ (Pi.single (0 : Fin 3) (1 : ℚ))))⁻¹
        = 5/36 := by
  have hdet : sineHankel3.det = 5/108 := by
    simp [sineHankel3, Matrix.det_fin_three]
    norm_num
  have hinv : sineHankel3⁻¹ 0 0 = 36/5 := by
    rw [Matrix.inv_def]
    simp [sineHankel3, Matrix.adjugate_fin_three, Matrix.det_fin_three]
    norm_num
  refine ⟨hdet, ?_, hinv, ?_⟩
  · rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  · have : dotProduct (Pi.single 0 1)
        (Matrix.mulVec sineHankel3⁻¹ (Pi.single (0 : Fin 3) (1 : ℚ))) = sineHankel3⁻¹ 0 0 := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [this, hinv]
    norm_num

end Zeta23Scaffold


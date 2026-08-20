/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Statement: Inverse-matrix cross-check: (M^{-1})_{00} = 36/5 for the sine-kernel Hankel matrix, so 1/(e_0^T M^{-1} e_0) = 5/36 agrees with the determinant-ratio Christoffel value.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

/-- The `3 × 3` sine-kernel Hankel matrix. -/
def christoffelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The determinant of the sine-kernel Hankel matrix is `5/108`. -/
theorem christoffelM_det : christoffelM.det = 5/108 := by
  simp [christoffelM, Matrix.det_fin_three]
  norm_num

/-- Inverse-matrix cross-check for the Christoffel function: the Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` is invertible (its determinant is
`5/108 ≠ 0`) and `(M⁻¹) 0 0 = 36/5`, so `1 / (eᵀ₀ M⁻¹ e₀) = 5/36`, matching the
determinant-ratio Christoffel value `Λ₂(0;1) = 5/36`. -/
theorem christoffel_inverse_form :
    IsUnit christoffelM.det ∧ christoffelM.det = 5/108 ∧ christoffelM⁻¹ 0 0 = 36/5 ∧
      (dotProduct (Pi.single 0 1) (christoffelM⁻¹.mulVec (Pi.single 0 1)))⁻¹
        = (5/36 : ℚ) := by
  have hdet : christoffelM.det = 5/108 := christoffelM_det
  have hinv : christoffelM⁻¹ 0 0 = 36/5 := by
    rw [Matrix.inv_def, Matrix.smul_apply, hdet, Matrix.adjugate_fin_three]
    simp [christoffelM]
    norm_num
  refine ⟨?_, hdet, hinv, ?_⟩
  · rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply, hinv]

end Zeta23Scaffold


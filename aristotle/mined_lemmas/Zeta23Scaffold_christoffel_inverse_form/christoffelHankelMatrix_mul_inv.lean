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

theorem christoffelHankelMatrix_mul_inv :
    christoffelHankelMatrix * christoffelHankelInv = 1 := by
  simp [christoffelHankelMatrix, christoffelHankelInv, Matrix.one_fin_three]
  norm_num

/-- Inverse-matrix cross-check for the Christoffel function: the sine-kernel Hankel
matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` is invertible (its determinant is
`5/108 ≠ 0`) and `(M⁻¹) 0 0 = 36/5`, so `1 / (eᵀ₀ M⁻¹ e₀) = 5/36`, agreeing with the
determinant-ratio (Hankel) value of `Λ₂(0;1)`. -/

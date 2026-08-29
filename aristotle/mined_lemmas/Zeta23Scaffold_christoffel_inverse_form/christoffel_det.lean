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

/-- The sine-kernel Hankel matrix of order 3 (moments `1, 1, 4/3, 2, 13/4`). -/

theorem christoffel_det : christoffelHankelMatrix.det = 5 / 108 := by
  simp [christoffelHankelMatrix, Matrix.det_fin_three]
  norm_num

/-- Inverse-matrix cross-check for the Christoffel function.

The Hankel matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` has determinant `5/108 ≠ 0`,
hence is invertible, and its inverse satisfies `(M⁻¹) 0 0 = 36/5`.  Consequently
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, which agrees with the determinant-ratio (Hankel-ratio) value
`Λ₂(0;1) = 5/36` of the Christoffel function. -/

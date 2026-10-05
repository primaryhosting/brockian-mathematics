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

theorem christoffel_inv_eq : christoffelM⁻¹ = christoffelMinv :=
  Matrix.inv_eq_right_inv christoffel_mul_inv

/--
Inverse-matrix cross-check for the Christoffel function: for the sine-kernel Hankel
matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]`, the matrix `M` is invertible
(its determinant is `5/108 ≠ 0`) and `(M⁻¹) 0 0 = 36/5`.  Consequently
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio (Hankel-ratio) value of
`Λ₂(0;1)`.
-/

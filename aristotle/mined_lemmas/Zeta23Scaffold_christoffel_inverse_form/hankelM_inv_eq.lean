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

/-- The 3×3 sine-kernel Hankel matrix of moments. -/

lemma hankelM_inv_eq : hankelM⁻¹ = hankelMinv :=
  Matrix.inv_eq_right_inv hankelM_mul_inv

/--
**Christoffel inverse form.**  The sine-kernel Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` has determinant `5/108 ≠ 0`, hence is
invertible, and `(M⁻¹) 0 0 = 36/5`.  Consequently the classical Christoffel value
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio definition of `Λ₂(0;1)`.
-/

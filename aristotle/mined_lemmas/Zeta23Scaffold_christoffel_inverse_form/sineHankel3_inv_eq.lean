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

lemma sineHankel3_inv_eq : sineHankel3⁻¹ = sineHankel3Inv :=
  Matrix.inv_eq_right_inv sineHankel3_mul_inv

/--
**Christoffel inverse form.**  For the `3 × 3` sine-kernel Hankel matrix
`M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` over `ℚ`, the determinant is `5/108`
(hence `M` is invertible), the `(0,0)` entry of `M⁻¹` equals `36/5`, and therefore
the classical Christoffel value `1 / (eᵀ₀ M⁻¹ e₀)` equals `5/36`, matching the
determinant-ratio definition of `Λ₂(0;1)`.
-/

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

def e0 : Fin 3 → ℚ := Pi.single 0 1

/--
**Christoffel inverse form.**

The sine-kernel Hankel matrix `M = !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]` is invertible
(its determinant is `5/108 ≠ 0`), and the `(0,0)` entry of its inverse equals `36/5`.
Equivalently `e₀ᵀ M⁻¹ e₀ = 36/5`, so the classical Christoffel value
`1 / (e₀ᵀ M⁻¹ e₀)` equals `5/36`, agreeing with the determinant-ratio (Hankel-ratio)
value of `Λ₂(0;1)`.
-/

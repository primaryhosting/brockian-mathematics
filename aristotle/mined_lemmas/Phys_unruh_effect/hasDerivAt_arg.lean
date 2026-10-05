/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to come before any module docstring, so the required header
-- above is an ordinary block comment.)

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The uniformly accelerated (Rindler) worldline

In `(1+1)`-dimensional Minkowski space with metric `-c² dt² + dx²`, the worldline of an
observer with constant proper acceleration `a`, parameterised by proper time `τ`, is

`t(τ) = (c/a) sinh (a τ / c)`,  `x(τ) = (c²/a) cosh (a τ / c)`.
-/

/-- Minkowski time coordinate of the uniformly accelerated observer, as a function of
proper time. -/

private lemma hasDerivAt_arg (τ : ℝ) :
    HasDerivAt (fun s : ℝ => a * s / c) (a / c) τ := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_id τ).const_mul a).div_const c


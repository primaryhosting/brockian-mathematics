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

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-!
## The Rindler worldline

A uniformly accelerated observer with proper acceleration `a` moves on the Rindler
hyperbola, parametrised by proper time `τ`:
`t(τ) = (c/a) sinh (a τ / c)`, `x(τ) = (c²/a) cosh (a τ / c)`.
-/

/-- Minkowski time coordinate of the uniformly accelerated (Rindler) observer, as a
function of its proper time. -/

theorem hasDerivAt_rindlerPos_deriv (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Real.sinh (a * s / c)) (a * Real.cosh (a * τ / c)) τ := by
  have h := ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_arg a c τ)).const_mul c
  convert h using 1
  field_simp

/-- The Rindler worldline is parametrised by proper time: its four-velocity has Minkowski
square `c² (dt/dτ)² − (dx/dτ)² = c²`. -/

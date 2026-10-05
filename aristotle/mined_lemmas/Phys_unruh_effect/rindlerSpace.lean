/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A uniformly accelerated observer in the Minkowski vacuum perceives a thermal bath at the
Unruh temperature `T = ℏ a / (2 π c k_B)`.

The file develops the statement in three layers.

1. *Kinematics of the Rindler worldline.*  The hyperbolic worldline
   `x⁰(τ) = (c²/a) sinh (a τ / c)`, `x¹(τ) = (c²/a) cosh (a τ / c)` is parametrised by proper
   time and has constant proper acceleration of magnitude `a`
   (`Phys.rindler_fourVelocity_normalized`, `Phys.rindler_properAcceleration`).
2. *Thermality from imaginary-time periodicity.*  The Minkowski interval between two points of
   this worldline depends only on the proper-time difference, and its analytic continuation
   `Phys.rindlerIntervalC` is periodic in imaginary proper time with period `2 π c / a`
   (`Phys.rindler_interval_eq`, `Phys.rindlerIntervalC_periodic`).  This is the KMS condition,
   whose period is `ℏ / (k_B T)`; equating the two periods yields the Unruh temperature.
3. *The Unruh temperature itself* (`Phys.unruhTemperature`) together with the detailed-balance
   relation, its uniqueness, and the resulting Planck spectrum (`Phys.unruh_effect`).
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

namespace Phys

/-! ## The Unruh temperature and the Planck spectrum -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with a uniformly
accelerated observer of proper acceleration `a`, where `ℏ` is the reduced Planck
constant, `c` the speed of light and `k_B` Boltzmann's constant. -/

noncomputable def rindlerSpace (c a τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- The time component of the four-velocity: `dx⁰/dτ = c cosh (a τ / c)`. -/

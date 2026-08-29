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

theorem rindler_interval_eq (c a t1 t2 : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    (rindlerSpace c a t1 - rindlerSpace c a t2) ^ 2
        - (rindlerTime c a t1 - rindlerTime c a t2) ^ 2
      = -(4 * c ^ 4 / a ^ 2) * (Real.sinh (a * (t1 - t2) / (2 * c))) ^ 2 := by
  unfold rindlerSpace rindlerTime
  set u1 := a * t1 / c with hu1
  set u2 := a * t2 / c with hu2
  have hy : a * (t1 - t2) / (2 * c) = (u1 - u2) / 2 := by rw [hu1, hu2]; field_simp
  have hcs : Real.cosh (u1 - u2) = 2 * Real.sinh ((u1 - u2) / 2) ^ 2 + 1 := by
    have h2 := Real.cosh_two_mul ((u1 - u2) / 2)
    have hs := Real.sinh_sq ((u1 - u2) / 2)
    have h3 : 2 * ((u1 - u2) / 2) = u1 - u2 := by ring
    rw [h3] at h2
    linarith
  have hsub := Real.cosh_sub u1 u2
  have e1 := Real.cosh_sq_sub_sinh_sq u1
  have e2 := Real.cosh_sq_sub_sinh_sq u2
  rw [hy]
  linear_combination (c ^ 2 / a) ^ 2 * e1 + (c ^ 2 / a) ^ 2 * e2 + 2 * (c ^ 2 / a) ^ 2 * hsub
    - 2 * (c ^ 2 / a) ^ 2 * hcs

/-- On real proper-time separations the complexified interval agrees with the Minkowski
interval along the worldline. -/

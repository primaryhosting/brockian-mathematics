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

theorem rindlerIntervalC_periodic (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) (z : ℂ) :
    rindlerIntervalC c a (z + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ))
      = rindlerIntervalC c a z := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold rindlerIntervalC
  have harg : (a : ℂ) * (z + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ)) / (2 * (c : ℂ))
      = (a : ℂ) * z / (2 * (c : ℂ)) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi,
    Complex.sin_pi]
  ring

/-! ## The Unruh effect -/

/--
**The Unruh effect.**

For a uniformly accelerated observer with proper acceleration `a > 0`, the Minkowski vacuum
appears as a thermal bath at the Unruh temperature `T = ℏ a / (2 π c k_B)`.

The statement packages the characteristic properties of this temperature:

* `T` is positive and equals `ℏ a / (2 π c k_B)`;
* **KMS condition from the worldline geometry**: the analytically continued interval along the
  accelerated worldline is periodic in imaginary proper time with period `ℏ / (k_B T)`, i.e.
  `ℏ β`, which is precisely the thermality criterion at temperature `T`;
* **detailed balance**: the Boltzmann weight `exp (-E / (k_B T))` at temperature `T` coincides,
  for every energy `E`, with the Rindler weight `exp (-2 π c E / (ℏ a))` dictated by that
  periodicity (equivalently, the Bogoliubov ratio `|β_ω|² / |α_ω|² = exp (-2 π c ω / a)`);
* `T` is the *unique* positive temperature satisfying the detailed-balance relation;
* **Planck spectrum**: the response of the accelerated detector,
  `1 / (exp (2 π c ω / a) - 1)`, is exactly the Planck occupation number at temperature `T`;
* the temperature is proportional to the acceleration: `T (λ a) = λ * T (a)`.
-/

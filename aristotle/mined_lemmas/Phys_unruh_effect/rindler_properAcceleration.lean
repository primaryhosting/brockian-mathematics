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

theorem rindler_properAcceleration (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    (deriv (fun s : ℝ => c * Real.sinh (a * s / c)) τ) ^ 2
      - c ^ 2 * (deriv (fun s : ℝ => Real.cosh (a * s / c)) τ) ^ 2 = a ^ 2 := by
  rw [(hasDerivAt_rindlerPos_deriv ha hc τ).deriv, (hasDerivAt_rindlerTime_deriv a c τ).deriv]
  have h := Real.cosh_sq_sub_sinh_sq (a * τ / c)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp
  nlinarith [h]

/-!
## Periodicity in imaginary proper time

Analytically continuing the Rindler worldline to complex proper time, it is periodic with
period `2 π i c / a`.  This imaginary-time periodicity is exactly the KMS condition at
inverse temperature `β = 2 π c / (ħ a)` in units where the Boltzmann factor is
`exp (-β ħ ω)`, and it is what forces the detected temperature to be the Unruh temperature.
-/

/-- Complexified Minkowski time of the Rindler observer. -/

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

theorem rindler_imaginary_time_periodic (ha : a ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    rindlerTimeC a c (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) = rindlerTimeC a c z ∧
    rindlerPosC a c (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) = rindlerPosC a c z := by
  constructor <;>
    simp [rindlerTimeC, rindlerPosC, arg_shift ha hc z, Complex.sinh, Complex.cosh,
      Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_neg]

/-!
## The Unruh temperature
-/

/-- The Unruh (Davies–Unruh) temperature `T = ℏ a / (2 π c k_B)` seen by an observer
undergoing uniform proper acceleration `a`, where `ℏ` is the reduced Planck constant,
`c` the speed of light and `k_B` Boltzmann's constant. -/

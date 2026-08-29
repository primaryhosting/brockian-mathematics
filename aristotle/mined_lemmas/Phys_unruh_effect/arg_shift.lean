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

private lemma arg_shift (ha : a ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    (a : ℂ) * (z + Complex.I * (rindlerImaginaryPeriod a c : ℝ)) / c
      = (a : ℂ) * z / c + 2 * Real.pi * Complex.I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [rindlerImaginaryPeriod, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp

/-- **Imaginary-time periodicity of the Rindler worldline.**  Continued to complex proper
time, the uniformly accelerated trajectory is periodic with imaginary period `2 π c / a`;
this is the KMS periodicity responsible for the thermal character of the Unruh effect. -/

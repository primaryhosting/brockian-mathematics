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

lemma unruh_bose_einstein {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) (ω : ℝ) :
    1 / (Real.exp (hbar * ω / (kB * unruhTemperature hbar a c kB)) - 1)
      = 1 / (Real.exp (2 * Real.pi * c * ω / a) - 1) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have : hbar * ω / (kB * unruhTemperature hbar a c kB) = 2 * Real.pi * c * ω / a := by
    rw [unruhTemperature]
    field_simp
  rw [this]

/-! ## Main theorem -/

/-- **The Unruh effect.**  An observer moving with constant proper acceleration `a`
through the Minkowski vacuum perceives a thermal bath at the Unruh temperature

`T = ℏ a / (2 π c k_B)`.

The statement collects:

1. the worldline `t(τ) = (c/a) sinh(aτ/c)`, `x(τ) = (c²/a) cosh(aτ/c)` is parameterised by
   proper time (four-velocity of Minkowski square `-c²`) and has constant proper
   acceleration `a` (four-acceleration of Minkowski square `a²`);
2. the Unruh temperature is positive;
3. it is the *unique* positive temperature whose thermal (KMS) imaginary-time period
   `ℏ/(k_B T)` equals the `2π c / a` periodicity of the Rindler propagator in imaginary
   proper time;
4. the corresponding Boltzmann factor and Bose–Einstein occupation numbers coincide with
   the Rindler ones;
5. the explicit formula `T = ℏ a / (2 π c k_B)`.
-/

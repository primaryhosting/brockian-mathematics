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

lemma unruh_kms_unique {hbar a c kB : ℝ} (hh : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) {T : ℝ} (hT : 0 < T) :
    hbar / (kB * T) = 2 * Real.pi * c / a ↔ T = unruhTemperature hbar a c kB := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : (kB * T) ≠ 0 := by positivity
  have h2 : a ≠ 0 := ne_of_gt ha
  have h3 : (2 * Real.pi * c * kB) ≠ 0 := by positivity
  rw [unruhTemperature]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    subst h
    field_simp

/-- **Detailed balance.** The Rindler thermal factor `exp (-2 π c ω / a)` of the Unruh
radiation is exactly the Boltzmann factor `exp (-ℏ ω / (k_B T))` at the Unruh
temperature. -/

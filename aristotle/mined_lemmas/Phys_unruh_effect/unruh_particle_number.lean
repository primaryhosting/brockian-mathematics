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

theorem unruh_particle_number (hbar a c kB omega A B : ℝ) (hhbar : 0 < hbar) (ha : 0 < a)
    (hc : 0 < c) (hkB : 0 < kB) (homega : 0 < omega) (hnorm : A - B = 1)
    (hratio : B = A * Real.exp (-(2 * Real.pi * c * omega / a))) :
    B = (Real.exp (hbar * omega / (kB * unruhTemperature hbar a c kB)) - 1)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxpos : 0 < 2 * Real.pi * c * omega / a := by positivity
  set x : ℝ := 2 * Real.pi * c * omega / a with hxdef
  have hqpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hqlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hone : (1 : ℝ) - Real.exp (-x) ≠ 0 := by linarith
  have hA : A * (1 - Real.exp (-x)) = 1 := by
    rw [hratio] at hnorm
    linear_combination hnorm
  have hB : B = Real.exp (-x) / (1 - Real.exp (-x)) := by
    rw [hratio]
    field_simp
    linear_combination hA
  have hexp : hbar * omega / (kB * unruhTemperature hbar a c kB) = x := by
    unfold unruhTemperature
    rw [hxdef]
    field_simp
  have hinv : Real.exp x = (Real.exp (-x))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [hexp, hinv, hB]
  field_simp

end Phys


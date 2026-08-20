/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Statement: State the Hawking temperature T = ℏc³/(8πGMk) of a Schwarzschild black hole.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Statement: State the Hawking temperature T = ℏc³/(8πGMk) of a Schwarzschild black hole.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

/-- The lapse function `f(r) = 1 - 2GM/(c²r)` of the Schwarzschild metric
`ds² = -f(r) c² dt² + f(r)⁻¹ dr² + r² dΩ²` for a black hole of mass `M`. -/

theorem metricLapse_schwarzschildRadius {G M c : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    metricLapse G M c (schwarzschildRadius G M c) = 0 := by
  have h : c ^ 2 * (2 * G * M / c ^ 2) = 2 * G * M := by
    field_simp
  simp only [metricLapse, schwarzschildRadius, h]
  have : (2 : ℝ) * G * M ≠ 0 := by
    simp [hG, hM]
  field_simp
  norm_num

/-- Derivative of the Schwarzschild lapse function: `f'(r) = 2GM/(c²r²)`. -/

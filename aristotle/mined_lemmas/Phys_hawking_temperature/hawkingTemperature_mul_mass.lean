import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
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

/-- The Schwarzschild radius (event-horizon radius) of a body of mass `M`,
`r_s = 2 G M / c ^ 2`. -/

theorem hawkingTemperature_mul_mass (hbar c G M k : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (hk : 0 < k) :
    hawkingTemperature hbar c G M k * M = hbar * c ^ 3 / (8 * Real.pi * G * k) := by
  have hG' : G ≠ 0 := ne_of_gt hG
  have hM' : M ≠ 0 := ne_of_gt hM
  have hk' : k ≠ 0 := ne_of_gt hk
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [hawking_temperature hbar c G M k hc hG hM hk]
  field_simp

/-- Heavier Schwarzschild black holes are colder: the Hawking temperature is strictly
decreasing in the mass (for positive `ℏ`). -/

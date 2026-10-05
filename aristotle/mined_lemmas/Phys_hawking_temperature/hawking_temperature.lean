/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The Schwarzschild radius `r_s = 2GM/c²` of a mass `M`. -/

theorem hawking_temperature (G M c hbar kB : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    hawkingTemp hbar c kB (surfaceGravity G M c)
      = hbar * c ^ 3 / (8 * Real.pi * G * M * kB) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hawkingTemp, surfaceGravity_eq G M c hG hM hc]
  field_simp
  ring

end Phys

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


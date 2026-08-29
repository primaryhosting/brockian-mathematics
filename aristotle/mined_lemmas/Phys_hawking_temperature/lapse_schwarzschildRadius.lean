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

/-- The Schwarzschild radius `r_s = 2GM/c²` of a body of mass `M`. -/

theorem lapse_schwarzschildRadius (G M c : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    lapse G M c (schwarzschildRadius G M c) = 0 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc
  unfold lapse schwarzschildRadius
  field_simp
  norm_num

/-- Derivative of the lapse function: `f'(r) = 2GM/(c² r²)`. -/

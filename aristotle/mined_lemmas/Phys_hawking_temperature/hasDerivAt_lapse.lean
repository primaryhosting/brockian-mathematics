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

theorem hasDerivAt_lapse (G M c r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (lapse G M c) (2 * G * M / (c ^ 2 * r ^ 2)) r := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h := (hinv.const_mul (2 * G * M / c ^ 2)).const_sub 1
  have hfun : (fun x : ℝ => 1 - 2 * G * M / c ^ 2 * x⁻¹) = lapse G M c := by
    funext x
    unfold lapse
    field_simp
  rw [hfun] at h
  convert h using 1
  field_simp

/-- The surface gravity `κ = (c²/2) f'(r_s)` of the Schwarzschild horizon. -/

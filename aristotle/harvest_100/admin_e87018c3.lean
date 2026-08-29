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
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The lapse function `f(r) = 1 - 2GM/(c²r)` appearing in the Schwarzschild metric
`ds² = -f(r) c² dt² + f(r)⁻¹ dr² + r² dΩ²`. -/
noncomputable def lapse (G M c : ℝ) (r : ℝ) : ℝ := 1 - 2 * G * M / (c ^ 2 * r)

/-- The lapse function vanishes exactly at the horizon `r = r_s` (for `M ≠ 0`). -/
theorem lapse_schwarzschildRadius (G M c : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    lapse G M c (schwarzschildRadius G M c) = 0 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc
  unfold lapse schwarzschildRadius
  field_simp
  norm_num

/-- Derivative of the lapse function: `f'(r) = 2GM/(c² r²)`. -/
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
noncomputable def surfaceGravity (G M c : ℝ) : ℝ :=
  c ^ 2 / 2 * deriv (lapse G M c) (schwarzschildRadius G M c)

/-- The surface gravity of a Schwarzschild black hole equals `c⁴/(4GM)`. -/
theorem surfaceGravity_eq (G M c : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c = c ^ 4 / (4 * G * M) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc
  have hrs : schwarzschildRadius G M c ≠ 0 := by
    unfold schwarzschildRadius
    exact div_ne_zero (by simpa using mul_ne_zero (mul_ne_zero two_ne_zero hG) hM) hc2
  have h := (hasDerivAt_lapse G M c _ hc hrs).deriv
  unfold surfaceGravity
  rw [h]
  unfold schwarzschildRadius
  field_simp
  ring

/-- The Hawking temperature of a black hole with surface gravity `κ`, given by
`T = ℏκ/(2πck_B)`. -/
noncomputable def hawkingTemperatureOfSurfaceGravity (hbar c kB kappa : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * kB)

/-- The Hawking temperature of a Schwarzschild black hole of mass `M`. -/
noncomputable def hawkingTemperature (hbar G M c kB : ℝ) : ℝ :=
  hawkingTemperatureOfSurfaceGravity hbar c kB (surfaceGravity G M c)

/-- **Hawking temperature of a Schwarzschild black hole.**

For a Schwarzschild black hole of mass `M`, the surface gravity of the horizon is
`κ = (c²/2) f'(r_s) = c⁴/(4GM)`, and the associated Hawking temperature
`T = ℏκ/(2πc k_B)` is

`T = ℏc³ / (8π G M k_B)`. -/
theorem hawking_temperature (hbar G M c kB : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    hawkingTemperature hbar G M c kB = hbar * c ^ 3 / (8 * Real.pi * G * M * kB) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold hawkingTemperature hawkingTemperatureOfSurfaceGravity
  rw [surfaceGravity_eq G M c hG hM hc]
  field_simp
  ring

end Phys


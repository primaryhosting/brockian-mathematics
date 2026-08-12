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
noncomputable def metricLapse (G M c r : ℝ) : ℝ := 1 - 2 * G * M / (c ^ 2 * r)

/-- The Schwarzschild radius `r_s = 2GM/c²`, i.e. the location of the event horizon
(the positive root of the lapse function). -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity `κ = c⁴/(4GM)` of a Schwarzschild black hole. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- The Hawking/Unruh temperature associated with a surface gravity `κ`:
`T = ℏκ/(2πck)`, where `k` is Boltzmann's constant. -/
noncomputable def hawkingTemperatureOf (hbar kappa c kB : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * kB)

/-- The lapse function vanishes exactly at the Schwarzschild radius. -/
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
theorem hasDerivAt_metricLapse (G M c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (metricLapse G M c) (2 * G * M / (c ^ 2 * r ^ 2)) r := by
  have h := ((hasDerivAt_inv hr).const_mul (2 * G * M / c ^ 2)).const_sub 1
  have hfun : (fun x : ℝ => 1 - 2 * G * M / c ^ 2 * x⁻¹) = metricLapse G M c := by
    funext x
    simp only [metricLapse, div_eq_mul_inv, mul_inv]
    ring
  rw [hfun] at h
  convert h using 1
  field_simp

/-- The surface gravity is `κ = (c²/2) f'(r_s)`, evaluated at the horizon. -/
theorem surfaceGravity_eq_lapse_deriv {G M c : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c
      = c ^ 2 / 2 * deriv (metricLapse G M c) (schwarzschildRadius G M c) := by
  have hrs : schwarzschildRadius G M c ≠ 0 := by
    simp only [schwarzschildRadius]
    intro h
    rcases (div_eq_zero_iff.mp h) with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h3 | h3
        · norm_num at h3
        · exact hG h3
      · exact hM h''
    · exact hc (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h')
  rw [(hasDerivAt_metricLapse G M c hrs).deriv]
  simp only [schwarzschildRadius, surfaceGravity]
  have h2 : (2 : ℝ) * G * M ≠ 0 := by simp [hG, hM]
  field_simp
  ring

/-- **Hawking temperature of a Schwarzschild black hole.**

For a black hole of mass `M`, the horizon surface gravity is `κ = c⁴/(4GM)`, and the
associated thermal (Hawking) temperature `T = ℏκ/(2πck)` is

`T = ℏc³/(8πGMk)`,

where `ℏ` is the reduced Planck constant, `c` the speed of light, `G` Newton's constant
and `k` Boltzmann's constant. -/
theorem hawking_temperature {hbar c G M kB : ℝ} (hc : c ≠ 0) (hG : G ≠ 0) (hM : M ≠ 0)
    (hkB : kB ≠ 0) :
    hawkingTemperatureOf hbar (surfaceGravity G M c) c kB
      = hbar * c ^ 3 / (8 * Real.pi * G * M * kB) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [hawkingTemperatureOf, surfaceGravity]
  field_simp
  ring

end Phys

#print axioms Phys.hawking_temperature
#print axioms Phys.surfaceGravity_eq_lapse_deriv
#print axioms Phys.metricLapse_schwarzschildRadius


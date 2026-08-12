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

/-- The Schwarzschild radius (event-horizon radius) of a black hole of mass `M`,
`r_s = 2 G M / c²`. -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity of a Schwarzschild black hole of mass `M`,
`κ = c⁴ / (4 G M)`, equivalently `c² / (2 r_s)`. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- The surface gravity expressed through the Schwarzschild radius:
`κ = c² / (2 r_s)`. -/
theorem surfaceGravity_eq_of_schwarzschildRadius
    {G M c : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c = c ^ 2 / (2 * schwarzschildRadius G M c) := by
  unfold surfaceGravity schwarzschildRadius
  field_simp
  ring

/-- The Hawking temperature of a black hole with surface gravity `κ`, as given by the
Hawking–Unruh relation `T = ℏ κ / (2 π c k)`, where `ℏ` is the reduced Planck constant,
`c` the speed of light and `k` the Boltzmann constant. -/
noncomputable def hawkingTemperatureOfSurfaceGravity (hbar kappa c k : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * k)

/-- **Hawking temperature of a Schwarzschild black hole.**

For any reduced Planck constant `ℏ` and positive values of the speed of light `c`, Newton's
constant `G`, the black-hole mass `M` and Boltzmann's constant `k`, the Hawking–Unruh
temperature `T = ℏ κ / (2 π c k)` associated with the Schwarzschild surface gravity
`κ = c⁴ / (4 G M)` is
`T = ℏ c³ / (8 π G M k)`. -/
theorem hawking_temperature
    {hbar c G M k : ℝ} (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) (hk : 0 < k) :
    hawkingTemperatureOfSurfaceGravity hbar (surfaceGravity G M c) c k
      = hbar * c ^ 3 / (8 * Real.pi * G * M * k) := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have hG' : G ≠ 0 := ne_of_gt hG
  have hM' : M ≠ 0 := ne_of_gt hM
  have hk' : k ≠ 0 := ne_of_gt hk
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold hawkingTemperatureOfSurfaceGravity surfaceGravity
  field_simp
  ring

end Phys

#print axioms Phys.hawking_temperature


import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- Schwarzschild radius of a body of mass `M`: `r_s = 2 G M / c ^ 2`. -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- Surface gravity at the horizon of a Schwarzschild black hole,
`κ = c ^ 4 / (4 G M)`. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- The surface gravity expressed through the Schwarzschild radius: `κ = c ^ 2 / (2 r_s)`. -/
theorem surfaceGravity_eq_of_schwarzschildRadius (G M c : ℝ) :
    surfaceGravity G M c = c ^ 2 / (2 * schwarzschildRadius G M c) := by
  unfold surfaceGravity schwarzschildRadius
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    · rcases eq_or_ne M 0 with hM | hM
      · simp [hM]
      · field_simp
        ring

/-- The Hawking temperature associated with the horizon surface gravity `κ` of a
Schwarzschild black hole, in terms of the reduced Planck constant `ℏ`, the speed of
light `c` and Boltzmann's constant `k`: `T = ℏ κ / (2 π c k)`. -/
noncomputable def hawkingTemperature (hbar c k G M : ℝ) : ℝ :=
  hbar * surfaceGravity G M c / (2 * π * c * k)

/-- **Hawking temperature of a Schwarzschild black hole.**

For a Schwarzschild black hole of mass `M`, the temperature obtained from the horizon
surface gravity `κ = c ^ 4 / (4 G M)` via `T = ℏ κ / (2 π c k)` is

`T = ℏ c ^ 3 / (8 π G M k)`.

The identity holds for all real values of the constants (no nonvanishing hypotheses are
needed, since division by zero is `0` in Lean). -/
theorem hawking_temperature (hbar c k G M : ℝ) :
    hawkingTemperature hbar c k G M = hbar * c ^ 3 / (8 * π * G * M * k) := by
  unfold hawkingTemperature surfaceGravity
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · field_simp
    ring

/-- With all physical constants positive, the Hawking temperature is positive and
inversely proportional to the mass. -/
theorem hawkingTemperature_pos {hbar c k G M : ℝ} (hbar_pos : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k) (hG : 0 < G) (hM : 0 < M) : 0 < hawkingTemperature hbar c k G M := by
  rw [hawking_temperature]
  have hpi : 0 < π := Real.pi_pos
  positivity

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


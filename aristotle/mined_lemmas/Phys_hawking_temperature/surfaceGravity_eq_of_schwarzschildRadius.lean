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

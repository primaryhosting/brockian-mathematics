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

theorem hawking_temperature (hbar c k G M : ℝ) :
    hawkingTemperature hbar c k G M = hbar * c ^ 3 / (8 * π * G * M * k) := by
  unfold hawkingTemperature surfaceGravity
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · field_simp
    ring

/-- With all physical constants positive, the Hawking temperature is positive and
inversely proportional to the mass. -/

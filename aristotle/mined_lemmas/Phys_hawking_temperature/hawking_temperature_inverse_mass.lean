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

/-- The surface gravity `κ = c⁴ / (4 G M)` at the horizon `r = 2GM/c²` of a
Schwarzschild black hole of mass `M`. -/

theorem hawking_temperature_inverse_mass (hbar c G M kB : ℝ)
    (hc : c ≠ 0) (hG : G ≠ 0) (hM : M ≠ 0) (hkB : kB ≠ 0) :
    temperatureOfSurfaceGravity hbar (surfaceGravity G (2 * M) c) c kB
      = temperatureOfSurfaceGravity hbar (surfaceGravity G M c) c kB / 2 := by
  rw [hawking_temperature hbar c G (2 * M) kB hc hG (by simpa using hM) hkB,
    hawking_temperature hbar c G M kB hc hG hM hkB]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Phys


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

theorem surfaceGravity_eq (G M c : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c = c ^ 4 / (4 * G * M) := by
  unfold surfaceGravity schwarzschildRadius
  field_simp
  ring

/-- **Hawking temperature of a Schwarzschild black hole.**

For a Schwarzschild black hole of mass `M`, the temperature obtained from the horizon
surface gravity `κ = c²/(2 r_s)` via `T = ℏκ/(2π c k)` is

`T = ℏ c³ / (8 π G M k)`. -/

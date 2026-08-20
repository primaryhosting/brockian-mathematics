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

theorem hawking_temperature_pos (hbar c G M kB : ℝ)
    (hbar_pos : 0 < hbar) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) (hkB : 0 < kB) :
    0 < temperatureOfSurfaceGravity hbar (surfaceGravity G M c) c kB := by
  rw [hawking_temperature hbar c G M kB hc.ne' hG.ne' hM.ne' hkB.ne']
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- The Hawking temperature is inversely proportional to the mass: doubling the
mass halves the temperature. -/

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

noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- The surface gravity expressed through the Schwarzschild radius: `κ = c ^ 2 / (2 r_s)`. -/

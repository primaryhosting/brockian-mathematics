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

noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity `κ = c²/(2 r_s)` at the horizon of a Schwarzschild black hole. -/

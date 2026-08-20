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

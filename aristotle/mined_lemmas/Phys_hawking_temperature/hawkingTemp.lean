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

noncomputable def hawkingTemp (hbar c kB kappa : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * kB)

/-- Surface gravity of a Schwarzschild black hole in terms of its mass: `κ = c⁴/(4GM)`. -/

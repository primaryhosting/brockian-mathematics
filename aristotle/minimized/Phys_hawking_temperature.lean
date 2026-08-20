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

noncomputable def temperatureOfSurfaceGravity (hbar kappa c kB : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * kB)

/-- **Hawking temperature of a Schwarzschild black hole.**

Feeding the Schwarzschild surface gravity `κ = c⁴/(4GM)` into the Hawking–Unruh
relation `T = ℏκ/(2πck_B)` gives

`T = ℏ c³ / (8 π G M k_B)`. -/

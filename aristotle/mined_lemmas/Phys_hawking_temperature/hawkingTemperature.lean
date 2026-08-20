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

noncomputable def hawkingTemperature (hbar c k G M : ℝ) : ℝ :=
  hbar * surfaceGravity G M c / (2 * π * c * k)

/-- **Hawking temperature of a Schwarzschild black hole.**

For a Schwarzschild black hole of mass `M`, the temperature obtained from the horizon
surface gravity `κ = c ^ 4 / (4 G M)` via `T = ℏ κ / (2 π c k)` is

`T = ℏ c ^ 3 / (8 π G M k)`.

The identity holds for all real values of the constants (no nonvanishing hypotheses are
needed, since division by zero is `0` in Lean). -/

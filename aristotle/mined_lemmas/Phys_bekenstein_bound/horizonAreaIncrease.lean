/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- The Bekenstein bound value `2 π k R E / (ℏ c)`: the maximal entropy of a physical
system of radius `R` and total energy `E`, expressed with Boltzmann's constant `k`,
the reduced Planck constant `ℏ` and the speed of light `c`. -/

noncomputable def horizonAreaIncrease (G c E R : ℝ) : ℝ :=
  8 * π * G * E * R / c ^ 4

/-- The Bekenstein–Hawking entropy associated with the horizon-area increase caused by
absorbing a body of energy `E` and radius `R` is exactly the Bekenstein bound value. -/

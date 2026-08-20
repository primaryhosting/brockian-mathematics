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

noncomputable def bekensteinBoundValue (k hbar c R E : ℝ) : ℝ :=
  2 * π * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy `k c³ A / (4 ℏ G)` of a black-hole horizon of area `A`. -/

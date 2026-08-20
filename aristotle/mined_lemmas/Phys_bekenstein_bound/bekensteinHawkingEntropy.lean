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

noncomputable def bekensteinHawkingEntropy (k hbar G c A : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * hbar * G)

/-- The increase `8 π G E R / c⁴` of the horizon area of a black hole that absorbs a body of
energy `E` whose centre is lowered to proper distance `R` from the horizon. -/

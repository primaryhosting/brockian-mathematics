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

theorem bekensteinHawkingEntropy_horizonAreaIncrease
    (k hbar G c R E : ℝ) (hhbar : hbar ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) :
    bekensteinHawkingEntropy k hbar G c (horizonAreaIncrease G c E R)
      = bekensteinBoundValue k hbar c R E := by
  unfold bekensteinHawkingEntropy horizonAreaIncrease bekensteinBoundValue
  field_simp
  ring

/-- **The Bekenstein bound.**  For a physical system of radius `R` and total energy `E`,
the entropy `S` obeys `S ≤ 2 π k R E / (ℏ c)`.

The bound is obtained from the generalized second law of thermodynamics: if the system is
absorbed by a black hole, the resulting increase in the Bekenstein–Hawking horizon entropy
must be at least the entropy `S` that the system carried (hypothesis `hGSL`), and the horizon
area grows by `8 π G E R / c⁴` (Bekenstein's construction).  Combining these facts, and the
fact that the entropy of that area increase is exactly `2 π k R E / (ℏ c)`, gives the bound. -/

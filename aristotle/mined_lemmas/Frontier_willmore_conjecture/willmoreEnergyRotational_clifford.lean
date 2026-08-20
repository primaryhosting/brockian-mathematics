/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/

theorem willmoreEnergyRotational_clifford (r : ℝ) (hr : 0 < r) :
    willmoreEnergyRotational (Real.sqrt 2 * r) r = 2 * π ^ 2 := by
  have hR : r < Real.sqrt 2 * r := by nlinarith [one_lt_sqrt_two]
  exact ((willmore_conjecture hr hR).2).2 rfl

/-- **The Clifford torus minimizes the Willmore energy among tori of revolution**:
`2π²` is the least element of the set of Willmore energies of tori of revolution. -/

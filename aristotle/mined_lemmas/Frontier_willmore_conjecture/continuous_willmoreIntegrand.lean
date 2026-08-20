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

theorem continuous_willmoreIntegrand (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    Continuous fun u : ℝ => (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
  have hcos : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have hD : 0 < R + r * Real.cos u := by nlinarith [Real.cos_le_one u]
  positivity

/-- The `u`-integral of the Willmore integrand over one full period. -/

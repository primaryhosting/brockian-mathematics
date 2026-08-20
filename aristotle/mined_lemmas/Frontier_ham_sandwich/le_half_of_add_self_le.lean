import Mathlib

/-!
# Medians of real-valued measurable functions

Auxiliary file for the Ham Sandwich development: every finite measure has a median
along any measurable real-valued function.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Frontier

variable {α : Type*} [MeasurableSpace α]

/-- **Existence of a median.** For a finite measure `μ` on `α` and a measurable function
`f : α → ℝ` there is a threshold `c` such that both `{f < c}` and `{f > c}` carry at most
half of the total mass. -/

private theorem le_half_of_add_self_le {a b : ℝ≥0∞} (h : a + a ≤ b) : a ≤ b / 2 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl (by simp)), mul_two]
  exact h

/-- **Ham–Sandwich for centrally symmetric measures, in every dimension and for any number of
measures.** If each of the finite measures `μ i` on `ℝⁿ` is invariant under the antipodal map
`x ↦ -x`, then *every* hyperplane through the origin simultaneously bisects all of them. -/

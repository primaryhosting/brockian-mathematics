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

theorem measurable_inner_left {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => inner ℝ v x :=
  ((innerSL ℝ v).continuous).measurable

/-- If a hyperplane bisects `μ`, then each of the two *closed* half-spaces it bounds carries at
least half of the mass of `μ`. -/

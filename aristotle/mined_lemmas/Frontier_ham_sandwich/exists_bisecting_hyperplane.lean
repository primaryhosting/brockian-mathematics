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

theorem exists_bisecting_hyperplane {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsFiniteMeasure μ] (v : EuclideanSpace ℝ (Fin n)) :
    ∃ c : ℝ, BisectedBy v c μ :=
  exists_median μ (measurable_inner_left v)

/-- Half of the total mass is an upper bound for anything whose "double" fits inside the total
mass. -/

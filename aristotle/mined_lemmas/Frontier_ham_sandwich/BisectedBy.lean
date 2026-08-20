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

theorem BisectedBy.half_le_closed {n : ℕ} {v : EuclideanSpace ℝ (Fin n)} {c : ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ] (h : BisectedBy v c μ) :
    μ univ / 2 ≤ μ {x | c ≤ inner ℝ v x} ∧ μ univ / 2 ≤ μ {x | inner ℝ v x ≤ c} := by
  have hmeas₁ : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x < c} :=
    measurable_inner_left v measurableSet_Iio
  have hmeas₂ : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | c < inner ℝ v x} :=
    measurable_inner_left v measurableSet_Ioi
  constructor
  · have hc : {x : EuclideanSpace ℝ (Fin n) | c ≤ inner ℝ v x}
        = {x | inner ℝ v x < c}ᶜ := by ext x; simp [not_lt]
    rw [hc, measure_compl hmeas₁ (measure_ne_top _ _)]
    refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
    calc μ univ / 2 + μ {x | inner ℝ v x < c} ≤ μ univ / 2 + μ univ / 2 := add_le_add le_rfl h.1
      _ = μ univ := ENNReal.add_halves _
  · have hc : {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x ≤ c}
        = {x | c < inner ℝ v x}ᶜ := by ext x; simp [not_lt]
    rw [hc, measure_compl hmeas₂ (measure_ne_top _ _)]
    refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
    calc μ univ / 2 + μ {x | c < inner ℝ v x} ≤ μ univ / 2 + μ univ / 2 := add_le_add le_rfl h.2
      _ = μ univ := ENNReal.add_halves _

/-- **A single finite measure on `ℝⁿ` can be bisected by a hyperplane** (the one-measure case of
the Ham–Sandwich theorem). The bisecting hyperplane can even be taken orthogonal to any
prescribed nonzero direction `v`: one only has to choose the offset `c` to be a median of the
linear functional `⟪v, ·⟫`. -/

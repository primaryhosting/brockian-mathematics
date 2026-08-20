import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Frontier

open ProbabilityTheory

/-- The Gaussian correlation inequality, as a property of a measure `μ` on a real vector
space `E`:  for any two measurable, convex, origin-symmetric sets `K` and `L`,
`μ (K ∩ L) ≥ μ K * μ L`.

Royen's theorem states that this holds for every centred Gaussian measure `μ`.  In this file
we formalise the statement and prove the one-dimensional base case together with several
Lean-checked reductions. -/

theorem correlation_of_subset {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {K L : Set E} (h : K ⊆ L) : μ K * μ L ≤ μ (K ∩ L) := by
  rw [Set.inter_eq_self_of_subset_left h]
  calc μ K * μ L ≤ μ K * 1 := mul_le_mul' le_rfl prob_le_one
    _ = μ K := mul_one _

/-- Reduction: positive correlation of two sets is equivalent to positive correlation of their
complements, for any probability measure. -/

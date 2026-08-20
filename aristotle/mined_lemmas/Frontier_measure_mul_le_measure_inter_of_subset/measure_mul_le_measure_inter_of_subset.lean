import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem measure_mul_le_measure_inter_of_subset (μ : Measure E) [IsProbabilityMeasure μ]
    {K L : Set E} (h : K ⊆ L ∨ L ⊆ K) : μ K * μ L ≤ μ (K ∩ L) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    exact mul_le_of_le_one_right' prob_le_one
  · rw [Set.inter_eq_self_of_subset_right h]
    exact mul_le_of_le_one_left' prob_le_one

end Elementary

section Dim1

/-- A symmetric convex subset of `ℝ` is a "downward closed set in absolute value":
if `a ∈ K` and `|b| ≤ |a|` then `b ∈ K`. -/

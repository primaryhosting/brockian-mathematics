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

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard (centered, identity–covariance) Gaussian measure on `Fin n → ℝ`:
the `n`-fold product of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem mul_le_measure_inter_of_subset {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {K L : Set α} (h : K ⊆ L ∨ L ⊆ K) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ K * μ L ≤ μ K * 1 := by gcongr; exact prob_le_one
      _ = μ K := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ K * μ L ≤ 1 * μ L := by gcongr; exact prob_le_one
      _ = μ L := one_mul _

/-- **Gaussian correlation inequality, base case (dimension one).**

For symmetric convex subsets `K`, `L` of the line, the standard Gaussian measure satisfies
`γ(K) · γ(L) ≤ γ(K ∩ L)`.  This is the base case of Royen's theorem. -/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem prob_mul_le_prob_inter_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K L : Set ℝ} (hK : IsSymmConvex K) (hL : IsSymmConvex L) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases subset_or_subset_of_isSymmConvex hK hL with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ K * μ L ≤ μ K * 1 := by gcongr; exact prob_le_one
      _ = μ K := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ K * μ L ≤ 1 * μ L := by gcongr; exact prob_le_one
      _ = μ L := one_mul _

/-- **Gaussian correlation inequality (Royen's theorem), one-dimensional base case.**
For every centered Gaussian measure `μ` on `ℝ` and all symmetric convex measurable sets
`K`, `L`, one has `μ K * μ L ≤ μ (K ∩ L)`. -/

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

theorem subset_or_subset_of_convex_symm {K L : Set ℝ} (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hy
    have hyx : |y| ≤ |x| := by
      by_contra hcon
      push_neg at hcon
      exact hxL (mem_of_abs_le_abs_of_convex_symm hL hLs hy (le_of_lt hcon))
    exact mem_of_abs_le_abs_of_convex_symm hK hKs hxK hyx

/-- **Gaussian correlation inequality, one-dimensional base case.**
For a centred Gaussian measure on `ℝ` (of arbitrary variance `v`), and any two measurable,
convex, origin-symmetric sets `K, L ⊆ ℝ`, we have `μ (K ∩ L) ≥ μ K * μ L`.

This is the base case `n = 1` of Royen's theorem: in dimension one, two symmetric convex sets
are automatically nested, and the inequality follows from `μ L ≤ 1`. -/

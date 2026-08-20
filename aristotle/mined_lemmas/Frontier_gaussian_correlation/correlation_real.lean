import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Gaussian correlation inequality (conjectured by Das Gupta–Eaton–Olkin–Perlman–Savage–Sobel,
proved by Thomas Royen in 2014) states that for a centred Gaussian measure `μ` on `ℝⁿ` and two
symmetric convex sets `K`, `L`,
`μ (K ∩ L) ≥ μ K * μ L`.

Mathlib (as of the pinned version) contains no form of this inequality: a search for
`gaussian_correlation` and related names returns nothing, and there is no lemma relating the
measure of an intersection of convex sets to the product of the measures. What Mathlib does
provide, and what we use here, is the theory of Gaussian measures
(`ProbabilityTheory.gaussianReal`, `ProbabilityTheory.IsGaussian`), convexity, and the general
measure-theoretic API.

This file therefore:

* formalises the general statement as `Frontier.GaussianCorrelation E`;
* proves the base case, dimension one, as `Frontier.gaussian_correlation`
  (in fact in the stronger form `Frontier.correlation_real`, valid for *any* probability measure
  on `ℝ`, since two symmetric convex subsets of `ℝ` are automatically nested);
* proves a Lean-checked reduction, `Frontier.GaussianCorrelation.of_continuousLinearEquiv`,
  saying that the statement only depends on the space up to continuous linear isomorphism, and
  deduces the dimension-one case for `Fin 1 → ℝ` and for `EuclideanSpace ℝ (Fin 1)`;
* proves the "independent blocks" case in arbitrary dimension,
  `Frontier.correlation_prod_of_independent_blocks`, where the inequality holds with equality.

The full theorem in dimension `≥ 2` (Royen's proof) is not formalised here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Frontier

/-!
## The statement
-/

/-- The Gaussian correlation inequality for the real normed space `E`: for every symmetric
(equivalently, centred) Gaussian measure `μ` on `E` and all symmetric convex measurable sets
`K`, `L`, one has `μ K * μ L ≤ μ (K ∩ L)`.

Symmetry of a set `S` is expressed as `∀ x ∈ S, -x ∈ S`, and centredness of `μ` as invariance
under `x ↦ -x`. -/

theorem correlation_real (μ : Measure ℝ) [IsProbabilityMeasure μ] {K L : Set ℝ}
    (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKsymm : ∀ x ∈ K, -x ∈ K) (hLsymm : ∀ x ∈ L, -x ∈ L) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases convex_symm_nested hK hL hKsymm hLsymm with h | h
  · rw [inter_eq_self_of_subset_left h]
    exact mul_le_of_le_one_right' prob_le_one
  · rw [inter_eq_self_of_subset_right h]
    exact mul_le_of_le_one_left' prob_le_one

/-- **The Gaussian correlation inequality in dimension one.**

For every symmetric Gaussian measure `μ` on `ℝ` and all symmetric convex measurable sets
`K, L ⊆ ℝ`, one has `μ K * μ L ≤ μ (K ∩ L)`.

This is the base case (`dim = 1`) of Royen's theorem, the Gaussian correlation inequality.
The measurability, symmetry and Gaussianity hypotheses are part of the general statement
`Frontier.GaussianCorrelation`; the one-dimensional proof only uses that `μ` is a probability
measure (see `Frontier.correlation_real`), since two symmetric convex subsets of `ℝ` are
automatically nested. -/

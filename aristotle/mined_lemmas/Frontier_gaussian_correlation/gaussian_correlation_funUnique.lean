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

theorem gaussian_correlation_funUnique : GaussianCorrelation (Fin 1 → ℝ) :=
  GaussianCorrelation.of_continuousLinearEquiv
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) gaussian_correlation

/-- The Gaussian correlation inequality on the one-dimensional Euclidean space
`EuclideanSpace ℝ (Fin 1)`. -/

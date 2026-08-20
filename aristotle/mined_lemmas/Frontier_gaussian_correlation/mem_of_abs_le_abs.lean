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

theorem mem_of_abs_le_abs {S : Set ℝ} (hS : Convex ℝ S) (hSsymm : ∀ x ∈ S, -x ∈ S)
    {a b : ℝ} (hb : b ∈ S) (hab : |a| ≤ |b|) : a ∈ S := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · have ha : a = 0 := by
      have : |a| ≤ 0 := by simpa [hb0] using hab
      simpa using abs_nonpos_iff.mp this
    simpa [ha, ← hb0] using hb
  · have hle : |a / b| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hb0)).mpr hab
    have h1 : -1 ≤ a / b := neg_le_of_abs_le hle
    have h2 : a / b ≤ 1 := le_of_abs_le hle
    set t : ℝ := (1 + a / b) / 2 with ht
    set s : ℝ := (1 - a / b) / 2 with hs
    have ht0 : 0 ≤ t := by simp only [ht]; linarith
    have hs0 : 0 ≤ s := by simp only [hs]; linarith
    have hts : t + s = 1 := by simp only [ht, hs]; ring
    have hmem := hS hb (hSsymm b hb) ht0 hs0 hts
    have heq : t • b + s • (-b) = a := by
      simp only [ht, hs, smul_eq_mul]
      field_simp
      ring
    rwa [heq] at hmem

/-- Two symmetric convex subsets of `ℝ` are nested. -/

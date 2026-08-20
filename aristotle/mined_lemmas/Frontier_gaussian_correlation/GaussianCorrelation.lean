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

theorem GaussianCorrelation.of_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (hF : GaussianCorrelation F) : GaussianCorrelation E := by
  intro μ hμ hsymm K L hKm hLm hKc hLc hKs hLs
  haveI : IsGaussian μ := hμ
  have he : Measurable (⇑e) := e.continuous.measurable
  have hes : Measurable (⇑e.symm) := e.symm.continuous.measurable
  have hnegE : Measurable (fun x : E => -x) := measurable_neg
  have hnegF : Measurable (fun y : F => -y) := measurable_neg
  set ν : Measure F := μ.map (⇑e) with hνdef
  have hνG : IsGaussian ν := isGaussian_map_of_measurable (L := (e : E →L[ℝ] F)) he
  have hνsymm : ν.map (fun y => -y) = ν := by
    rw [hνdef, Measure.map_map hnegF he,
      show ((fun y : F => -y) ∘ ⇑e) = (⇑e) ∘ (fun x : E => -x) by funext x; simp,
      ← Measure.map_map he hnegE, hsymm]
  set K' : Set F := ⇑e.symm ⁻¹' K with hK'
  set L' : Set F := ⇑e.symm ⁻¹' L with hL'
  have hK'm : MeasurableSet K' := hes hKm
  have hL'm : MeasurableSet L' := hes hLm
  have hK'c : Convex ℝ K' := hKc.linear_preimage (e.symm : F →ₗ[ℝ] E)
  have hL'c : Convex ℝ L' := hLc.linear_preimage (e.symm : F →ₗ[ℝ] E)
  have hK's : ∀ y ∈ K', -y ∈ K' := by
    intro y hy
    simp only [hK', mem_preimage, map_neg]
    exact hKs _ hy
  have hL's : ∀ y ∈ L', -y ∈ L' := by
    intro y hy
    simp only [hL', mem_preimage, map_neg]
    exact hLs _ hy
  have hpre : ∀ S : Set E, ⇑e ⁻¹' (⇑e.symm ⁻¹' S) = S := by
    intro S; ext x; simp
  have hνK : ν K' = μ K := by rw [hνdef, Measure.map_apply he hK'm, hpre]
  have hνL : ν L' = μ L := by rw [hνdef, Measure.map_apply he hL'm, hpre]
  have hνKL : ν (K' ∩ L') = μ (K ∩ L) := by
    rw [hνdef, Measure.map_apply he (hK'm.inter hL'm), Set.preimage_inter, hpre, hpre]
  have hmain := hF ν hνG hνsymm K' L' hK'm hL'm hK'c hL'c hK's hL's
  rwa [hνK, hνL, hνKL] at hmain

/-- The Gaussian correlation inequality on the one-dimensional space `Fin 1 → ℝ`. -/

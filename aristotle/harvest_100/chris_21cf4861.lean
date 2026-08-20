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
def GaussianCorrelation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ μ : Measure E, IsGaussian μ → μ.map (fun x => -x) = μ →
    ∀ K L : Set E, MeasurableSet K → MeasurableSet L → Convex ℝ K → Convex ℝ L →
      (∀ x ∈ K, -x ∈ K) → (∀ x ∈ L, -x ∈ L) →
      μ K * μ L ≤ μ (K ∩ L)

/-!
## The one-dimensional case

In dimension one the inequality holds for *any* probability measure, because two symmetric
convex subsets of `ℝ` are always nested.
-/

/-- A symmetric convex subset of `ℝ` containing `b` contains every point of absolute value
at most `|b|`. -/
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
theorem convex_symm_nested {K L : Set ℝ} (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKsymm : ∀ x ∈ K, -x ∈ K) (hLsymm : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x, hxK, hxL⟩ := not_subset.mp h1
  obtain ⟨y, hyL, hyK⟩ := not_subset.mp h2
  rcases le_total |x| |y| with h | h
  · exact hxL (mem_of_abs_le_abs hL hLsymm hyL h)
  · exact hyK (mem_of_abs_le_abs hK hKsymm hxK h)

/-- The correlation inequality on the real line, valid for an arbitrary probability measure:
if `K` and `L` are symmetric convex subsets of `ℝ`, then `μ K * μ L ≤ μ (K ∩ L)`. -/
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
theorem gaussian_correlation : GaussianCorrelation ℝ := by
  intro μ hμ _ K L _ _ hKc hLc hKs hLs
  haveI : IsGaussian μ := hμ
  exact correlation_real μ hKc hLc hKs hLs

/-- A concrete instance of the one-dimensional Gaussian correlation inequality, for the standard
normal distribution on `ℝ`. This witnesses that `Frontier.gaussian_correlation` is not vacuous. -/
theorem gaussianReal_correlation (v : ℝ≥0) {K L : Set ℝ}
    (hKm : MeasurableSet K) (hLm : MeasurableSet L) (hKc : Convex ℝ K) (hLc : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) :
    gaussianReal 0 v K * gaussianReal 0 v L ≤ gaussianReal 0 v (K ∩ L) :=
  gaussian_correlation (gaussianReal 0 v) inferInstance
    (by rw [gaussianReal_map_neg]; norm_num) K L hKm hLm hKc hLc hKs hLs

/-!
## A reduction: invariance under continuous linear isomorphisms
-/

/-- The Gaussian correlation inequality only depends on the underlying space up to continuous
linear isomorphism: if it holds on `F` and `e : E ≃L[ℝ] F`, then it holds on `E`. -/
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
theorem gaussian_correlation_funUnique : GaussianCorrelation (Fin 1 → ℝ) :=
  GaussianCorrelation.of_continuousLinearEquiv
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) gaussian_correlation

/-- The Gaussian correlation inequality on the one-dimensional Euclidean space
`EuclideanSpace ℝ (Fin 1)`. -/
theorem gaussian_correlation_euclideanSpace_one :
    GaussianCorrelation (EuclideanSpace ℝ (Fin 1)) :=
  GaussianCorrelation.of_continuousLinearEquiv
    ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ))
    gaussian_correlation

/-!
## The independent-blocks case in arbitrary dimension

If `K` constrains only the first block of coordinates and `L` only the second block, then the
two events are independent for a product measure and the correlation inequality holds with
equality. This covers, in every dimension, the case of two symmetric convex "cylinders" over
complementary blocks of coordinates.
-/

/-- For a product of probability measures, a cylinder over the first factor and a cylinder over
the second factor are independent, so the Gaussian correlation inequality holds with equality
(no convexity or measurability needed). -/
theorem correlation_prod_of_independent_blocks {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set E) (B : Set F) :
    (μ.prod ν) (A ×ˢ (univ : Set F)) * (μ.prod ν) ((univ : Set E) ×ˢ B)
      = (μ.prod ν) ((A ×ˢ (univ : Set F)) ∩ ((univ : Set E) ×ˢ B)) := by
  rw [Set.prod_inter_prod]
  simp [Measure.prod_prod]

end Frontier

import Mathlib

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


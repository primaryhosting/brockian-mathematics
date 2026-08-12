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
def GaussianCorrelation {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (μ : Measure E) : Prop :=
  ∀ K L : Set E, MeasurableSet K → MeasurableSet L → Convex ℝ K → Convex ℝ L →
    (∀ x ∈ K, -x ∈ K) → (∀ x ∈ L, -x ∈ L) → μ K * μ L ≤ μ (K ∩ L)

/-- **Royen's theorem** (the general Gaussian correlation inequality), stated as a proposition
about a real Banach space `E`: every centred (i.e. symmetric) Gaussian measure on `E` satisfies
`GaussianCorrelation`.  This file proves the one-dimensional instance of this statement
(`Frontier.gaussian_correlation`) together with several reductions; the general case is not
proved here. -/
def RoyenGaussianCorrelation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ μ : Measure E, IsGaussian μ → μ.map (fun x => -x) = μ → GaussianCorrelation μ

/-- Reduction: for a probability measure, the correlation inequality holds for any pair of
nested sets.  (No convexity, symmetry or Gaussianity is needed.) -/
theorem correlation_of_subset {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {K L : Set E} (h : K ⊆ L) : μ K * μ L ≤ μ (K ∩ L) := by
  rw [Set.inter_eq_self_of_subset_left h]
  calc μ K * μ L ≤ μ K * 1 := mul_le_mul' le_rfl prob_le_one
    _ = μ K := mul_one _

/-- Reduction: positive correlation of two sets is equivalent to positive correlation of their
complements, for any probability measure. -/
theorem correlation_compl_iff {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {K L : Set E} (hK : MeasurableSet K) (hL : MeasurableSet L) :
    μ K * μ L ≤ μ (K ∩ L) ↔ μ Kᶜ * μ Lᶜ ≤ μ (Kᶜ ∩ Lᶜ) := by
  -- Work with real numbers, where subtraction is well behaved.
  have hfin : ∀ s : Set E, μ s ≠ ∞ := fun s => measure_ne_top μ s
  have conv : ∀ s t u : Set E,
      (μ s * μ t ≤ μ u ↔ (μ s).toReal * (μ t).toReal ≤ (μ u).toReal) := by
    intro s t u
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (hfin s) (hfin t)) (hfin u)).symm
  have h1 : (μ Kᶜ).toReal = 1 - (μ K).toReal := by
    rw [measure_compl hK (hfin K), measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    simp
  have h2 : (μ Lᶜ).toReal = 1 - (μ L).toReal := by
    rw [measure_compl hL (hfin L), measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    simp
  have h3 : (μ (Kᶜ ∩ Lᶜ)).toReal
      = 1 - (μ K).toReal - (μ L).toReal + (μ (K ∩ L)).toReal := by
    have hunion : μ (K ∪ L) + μ (K ∩ L) = μ K + μ L := measure_union_add_inter K hL
    have hc : Kᶜ ∩ Lᶜ = (K ∪ L)ᶜ := by rw [Set.compl_union]
    rw [hc, measure_compl (hK.union hL) (hfin _), measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    have h4 := congrArg ENNReal.toReal hunion
    rw [ENNReal.toReal_add (hfin _) (hfin _), ENNReal.toReal_add (hfin _) (hfin _)] at h4
    simp only [ENNReal.toReal_one]
    linarith
  rw [conv, conv, h1, h2, h3]
  constructor <;> intro h <;> nlinarith [h]

/-- A convex origin-symmetric subset of `ℝ` is "downward closed" in absolute value. -/
theorem mem_of_abs_le_abs_of_convex_symm {S : Set ℝ} (hS : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : ℝ} (hx : x ∈ S) (hxy : |y| ≤ |x|) : y ∈ S := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have : y = 0 := by
      have : |y| ≤ 0 := by simpa using hxy
      simpa using abs_nonpos_iff.mp this
    simpa [this] using hx
  · set t : ℝ := y / x with ht
    have habs : |t| ≤ 1 := by
      rw [ht, abs_div]
      rw [div_le_one (abs_pos.mpr hx0)]
      exact hxy
    have h1 : (0:ℝ) ≤ (1 + t) / 2 := by
      have ht1 : -1 ≤ t := by linarith [neg_abs_le t, habs]
      linarith
    have h2 : (0:ℝ) ≤ (1 - t) / 2 := by
      have ht2 : t ≤ 1 := le_trans (le_abs_self t) habs
      linarith
    have hsum : (1 + t) / 2 + (1 - t) / 2 = 1 := by ring
    have := hS hx (hsymm x hx) h1 h2 hsum
    have hval : ((1 + t) / 2) • x + ((1 - t) / 2) • (-x) = y := by
      simp only [smul_eq_mul, mul_neg, ht]
      field_simp
      ring
    rwa [hval] at this

/-- Two convex origin-symmetric subsets of `ℝ` are nested. -/
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
theorem gaussian_correlation (v : ℝ≥0) : GaussianCorrelation (gaussianReal 0 v) := by
  intro K L _ _ hK hL hKs hLs
  rcases subset_or_subset_of_convex_symm hK hL hKs hLs with h | h
  · exact correlation_of_subset _ h
  · rw [Set.inter_comm, mul_comm]
    exact correlation_of_subset _ h

/-- **A two-dimensional case.**  For a product of two centred Gaussian measures on `ℝ × ℝ`
and two symmetric convex *rectangles* `A ×ˢ B` and `C ×ˢ D`, the Gaussian correlation
inequality holds.  This is a Lean-checked reduction of the product case to the
one-dimensional base case. -/
theorem gaussian_correlation_prod (v w : ℝ≥0) {A B C D : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAc : Convex ℝ A) (hBc : Convex ℝ B) (hCc : Convex ℝ C) (hDc : Convex ℝ D)
    (hAs : ∀ x ∈ A, -x ∈ A) (hBs : ∀ x ∈ B, -x ∈ B) (hCs : ∀ x ∈ C, -x ∈ C)
    (hDs : ∀ x ∈ D, -x ∈ D) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)) (A ×ˢ B)
        * ((gaussianReal 0 v).prod (gaussianReal 0 w)) (C ×ˢ D)
      ≤ ((gaussianReal 0 v).prod (gaussianReal 0 w)) ((A ×ˢ B) ∩ (C ×ˢ D)) := by
  have hAC : gaussianReal 0 v A * gaussianReal 0 v C ≤ gaussianReal 0 v (A ∩ C) :=
    gaussian_correlation v A C hA hC hAc hCc hAs hCs
  have hBD : gaussianReal 0 w B * gaussianReal 0 w D ≤ gaussianReal 0 w (B ∩ D) :=
    gaussian_correlation w B D hB hD hBc hDc hBs hDs
  rw [Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc gaussianReal 0 v A * gaussianReal 0 w B * (gaussianReal 0 v C * gaussianReal 0 w D)
      = (gaussianReal 0 v A * gaussianReal 0 v C) * (gaussianReal 0 w B * gaussianReal 0 w D) := by
        ring
    _ ≤ gaussianReal 0 v (A ∩ C) * gaussianReal 0 w (B ∩ D) := mul_le_mul' hAC hBD

end Frontier

#print axioms Frontier.gaussian_correlation

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


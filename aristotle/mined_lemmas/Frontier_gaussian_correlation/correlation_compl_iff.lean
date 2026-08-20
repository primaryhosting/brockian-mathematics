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

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma stIntegral_bumpUpper_le {α β δ : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    stIntegral (bumpUpper α β δ) ≤ (∫ t in α..β, stDensity t) + (2 / π) * (2 * δ) := by
  set a1 : ℝ := max 0 (α - δ) with ha1def
  set a2 : ℝ := min π (β + δ) with ha2def
  have ha1_0 : 0 ≤ a1 := le_max_left _ _
  have ha1_α : a1 ≤ α := max_le hα (by linarith)
  have ha1_ge : α - δ ≤ a1 := le_max_right _ _
  have ha2_π : a2 ≤ π := min_le_left _ _
  have ha2_β : β ≤ a2 := le_min hβ (by linarith)
  have ha2_le : a2 ≤ β + δ := min_le_right _ _
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => bumpUpper α β δ t * stDensity t)
      MeasureTheory.volume x y :=
    fun x y => ((continuous_bumpUpper α β δ).mul continuous_stDensity).intervalIntegrable x y
  have hsplit1 : (∫ t in (0:ℝ)..π, bumpUpper α β δ t * stDensity t)
      = (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t)
        + ∫ t in a1..π, bumpUpper α β δ t * stDensity t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 a1) (hint a1 π)).symm
  have hsplit2 : (∫ t in a1..π, bumpUpper α β δ t * stDensity t)
      = (∫ t in a1..a2, bumpUpper α β δ t * stDensity t)
        + ∫ t in a2..π, bumpUpper α β δ t * stDensity t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint a1 a2) (hint a2 π)).symm
  have hz1 : (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t) = 0 := by
    rcases le_or_gt (α - δ) 0 with hc | hc
    · rw [show a1 = 0 from max_eq_left hc]; simp
    · have hae : a1 = α - δ := max_eq_right hc.le
      rw [show (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t)
          = ∫ _t in (0:ℝ)..a1, (0:ℝ) from intervalIntegral.integral_congr ?_]
      · simp
      · intro t ht
        rw [uIcc_of_le ha1_0] at ht
        show bumpUpper α β δ t * stDensity t = 0
        rw [bumpUpper_eq_zero_left hδ (by rw [← hae]; exact ht.2), zero_mul]
  have hz2 : (∫ t in a2..π, bumpUpper α β δ t * stDensity t) = 0 := by
    rcases le_or_gt π (β + δ) with hc | hc
    · rw [show a2 = π from min_eq_left hc]; simp
    · have hae : a2 = β + δ := min_eq_right hc.le
      rw [show (∫ t in a2..π, bumpUpper α β δ t * stDensity t)
          = ∫ _t in a2..π, (0:ℝ) from intervalIntegral.integral_congr ?_]
      · simp
      · intro t ht
        rw [uIcc_of_le ha2_π] at ht
        show bumpUpper α β δ t * stDensity t = 0
        rw [bumpUpper_eq_zero_right hδ (by rw [← hae]; exact ht.1), zero_mul]
  have hmid : (∫ t in a1..a2, bumpUpper α β δ t * stDensity t) ≤ ∫ t in a1..a2, stDensity t := by
    apply intervalIntegral.integral_mono_on (le_trans ha1_α (le_trans hαβ ha2_β))
      (hint a1 a2) (continuous_stDensity.intervalIntegrable _ _)
    intro t _
    nlinarith [bumpUpper_le_one α β δ t, stDensity_nonneg t, bumpUpper_nonneg α β δ t]
  have hadd : (∫ t in a1..a2, stDensity t)
      = (∫ t in a1..α, stDensity t) + (∫ t in α..β, stDensity t) + ∫ t in β..a2, stDensity t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _)]
  have hb1 : (∫ t in a1..α, stDensity t) ≤ (2 / π) * δ := by
    have h := stDensity_integral_le ha1_α
    have h2 : (0:ℝ) < 2 / π := by positivity
    nlinarith
  have hb2 : (∫ t in β..a2, stDensity t) ≤ (2 / π) * δ := by
    have h := stDensity_integral_le ha2_β
    have h2 : (0:ℝ) < 2 / π := by positivity
    nlinarith
  unfold stIntegral
  rw [hsplit1, hsplit2, hz1, hz2]
  rw [hadd] at hmid
  linarith


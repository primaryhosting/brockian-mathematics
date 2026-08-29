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

lemma stIntegral_bumpLower_ge {α β δ : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    (∫ t in α..β, stDensity t) - (2 / π) * (2 * δ) ≤ stIntegral (bumpLower α β δ) := by
  have hpi : (0:ℝ) < 2 / π := by positivity
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => bumpLower α β δ t * stDensity t)
      MeasureTheory.volume x y :=
    fun x y => ((continuous_bumpLower α β δ).mul continuous_stDensity).intervalIntegrable x y
  have hnonneg : ∀ x y : ℝ, x ≤ y → 0 ≤ ∫ t in x..y, bumpLower α β δ t * stDensity t := by
    intro x y hxy
    exact intervalIntegral.integral_nonneg hxy
      (fun t _ => mul_nonneg (bumpLower_nonneg α β δ t) (stDensity_nonneg t))
  rcases lt_or_ge (β - δ) (α + δ) with hcase | hcase
  · have h1 : (∫ t in α..β, stDensity t) ≤ (2 / π) * (2 * δ) := by
      have h := stDensity_integral_le hαβ
      nlinarith
    have h2 : 0 ≤ stIntegral (bumpLower α β δ) := hnonneg 0 π Real.pi_pos.le
    linarith
  · set b1 : ℝ := α + δ with hb1
    set b2 : ℝ := β - δ with hb2
    have hb1_0 : 0 ≤ b1 := by rw [hb1]; linarith
    have hb2_π : b2 ≤ π := by rw [hb2]; linarith
    have hsplit1 : (∫ t in (0:ℝ)..π, bumpLower α β δ t * stDensity t)
        = (∫ t in (0:ℝ)..b1, bumpLower α β δ t * stDensity t)
          + ∫ t in b1..π, bumpLower α β δ t * stDensity t :=
      (intervalIntegral.integral_add_adjacent_intervals (hint 0 b1) (hint b1 π)).symm
    have hsplit2 : (∫ t in b1..π, bumpLower α β δ t * stDensity t)
        = (∫ t in b1..b2, bumpLower α β δ t * stDensity t)
          + ∫ t in b2..π, bumpLower α β δ t * stDensity t :=
      (intervalIntegral.integral_add_adjacent_intervals (hint b1 b2) (hint b2 π)).symm
    have hmid : (∫ t in b1..b2, bumpLower α β δ t * stDensity t)
        = ∫ t in b1..b2, stDensity t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hcase] at ht
      show bumpLower α β δ t * stDensity t = stDensity t
      rw [bumpLower_eq_one hδ ht.1 ht.2, one_mul]
    have hadd : (∫ t in α..β, stDensity t)
        = (∫ t in α..b1, stDensity t) + (∫ t in b1..b2, stDensity t)
          + ∫ t in b2..β, stDensity t := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _)]
    have hc1 : (∫ t in α..b1, stDensity t) ≤ (2 / π) * δ := by
      have h := stDensity_integral_le (show α ≤ b1 by rw [hb1]; linarith)
      rw [hb1] at h
      nlinarith
    have hc2 : (∫ t in b2..β, stDensity t) ≤ (2 / π) * δ := by
      have h := stDensity_integral_le (show b2 ≤ β by rw [hb2]; linarith)
      rw [hb2] at h
      nlinarith
    have hz1 : 0 ≤ ∫ t in (0:ℝ)..b1, bumpLower α β δ t * stDensity t := hnonneg 0 b1 hb1_0
    have hz2 : 0 ≤ ∫ t in b2..π, bumpLower α β δ t * stDensity t := hnonneg b2 π hb2_π
    unfold stIntegral
    rw [hsplit1, hsplit2, hmid]
    linarith

/-- The proportion of primes `p ≤ N` whose angle `θ p` lies in `[α, β]`. -/

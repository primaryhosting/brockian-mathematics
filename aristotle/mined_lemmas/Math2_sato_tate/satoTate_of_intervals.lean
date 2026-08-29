/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem satoTate_of_intervals {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi)
    (hI : SatoTateIntervals θ) : SatoTateEquidistributed θ := by
  intro f hf
  have hpi := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- uniform continuity of `f` on `[0, π]`
  have hcont : UniformContinuousOn f (Icc 0 Real.pi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hcont
  obtain ⟨η, hη, hηc⟩ := hcont (δ / 4) (by linarith)
  -- a grid fine enough
  set n : ℕ := ⌈Real.pi / η⌉₊ + 1 with hndef
  have hn : 0 < n := Nat.succ_pos _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpin : Real.pi / n < η := by
    have h1 : Real.pi / η ≤ (⌈Real.pi / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : Real.pi / η < (n : ℝ) := by rw [hndef]; push_cast; linarith
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hη] at h2
    linarith [h2]
  have hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi,
      |x - y| ≤ Real.pi / n → |f x - f y| ≤ δ / 4 := by
    intro x hx y hy hxy
    have : dist x y < η := by rw [Real.dist_eq]; linarith
    have := hηc x hx y hy this
    rw [Real.dist_eq] at this
    linarith
  -- the averages of the step function converge
  have hconv : Tendsto
      (fun X : ℕ => f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ))
          / (primesBelow X).card))
      atTop (𝓝 (f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (∫ x in (0 : ℝ)..grid n j, satoTateDensity x))) := by
    refine Tendsto.const_add _ (tendsto_finset_sum _ fun j hj => ?_)
    rw [Finset.mem_range] at hj
    exact ((hI 0 (grid n j) le_rfl (grid_nonneg n j) (grid_mem hn hj.le).2)).const_mul _
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (δ / 4) (by linarith)
  refine ⟨max N 3, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hPpos : (0 : ℝ) < (primesBelow X).card := by exact_mod_cast primesBelow_card_pos hX3
  set P : ℝ := ((primesBelow X).card : ℝ) with hP
  -- the step average, in two forms
  have hstep : (∑ p ∈ primesBelow X, stepFun f n (θ p)) / P
      = f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ)) / P) := by
    rw [sum_stepFun f n hrange X, add_div, Finset.sum_div]
    have hne : ((primesBelow X).card : ℝ) ≠ 0 := by rw [hP] at hPpos; exact ne_of_gt hPpos
    congr 1
    · rw [hP, mul_comm, mul_div_assoc, div_self hne, mul_one]
    · exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
  -- three error terms
  have h1 : |(∑ p ∈ primesBelow X, f (θ p)) / P
      - (∑ p ∈ primesBelow X, stepFun f n (θ p)) / P| ≤ δ / 4 := by
    rw [div_sub_div_same, abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos]
    have := abs_sum_sub_sum_stepFun hn hrange hunif X
    calc |(∑ p ∈ primesBelow X, f (θ p)) - ∑ p ∈ primesBelow X, stepFun f n (θ p)|
        ≤ P * (δ / 4) := this
      _ = δ / 4 * P := by ring
  have h2 := hN X hXN
  rw [Real.dist_eq] at h2
  have h3 := stepIntegral_bound hf hn hunif
  rw [Real.dist_eq]
  rw [hstep] at h1
  calc |(∑ p ∈ primesBelow X, f (θ p)) / P - ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x|
      ≤ δ / 4 + δ / 4 + δ / 4 := by
        rw [abs_le] at h1 h3 ⊢
        rw [abs_lt] at h2
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    _ < δ := by linarith

/-- The two formulations of Sato–Tate equidistribution agree, for angles in `[0, π]`. -/

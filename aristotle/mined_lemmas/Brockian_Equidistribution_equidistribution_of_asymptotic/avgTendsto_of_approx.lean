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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic

This file proves **Weyl's criterion**: if a real sequence `x` satisfies the asymptotic
exponential-sum estimate `∑_{n < N} e(h * xₙ) = o(N)` for every nonzero integer `h`, then `x`
is equidistributed modulo one, i.e. for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
indices `n < N` with `Int.fract (xₙ) ∈ [a, b)` tends to `b - a`.
-/

open Filter Finset MeasureTheory Metric Set Submodule
open scoped BigOperators Real Topology

namespace Brockian.Equidistribution

noncomputable section

/-- The image of a real sequence in the circle `ℝ / ℤ`. -/

lemma avgTendsto_of_approx (x : ℕ → ℝ) (F : C(AddCircle (1 : ℝ), ℂ))
    (h : ∀ ε > 0, ∃ G : C(AddCircle (1 : ℝ), ℂ), AvgTendsto x G ∧ ∀ t, ‖F t - G t‖ ≤ ε) :
    AvgTendsto x F := by
  rw [AvgTendsto, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨G, hG, hd⟩ := h (δ / 4) (by linarith)
  rw [AvgTendsto, Metric.tendsto_atTop] at hG
  obtain ⟨N₁, hN₁⟩ := hG (δ / 4) (by linarith)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have b1 : ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n)‖
      ≤ δ / 4 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖ ≤ N * (δ / 4) := by
      calc ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖
          ≤ ∑ n ∈ range N, ‖F (pts x n) - G (pts x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (δ / 4) := Finset.sum_le_sum fun n _ => hd _
        _ = N * (δ / 4) := by simp
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, (F (pts x n) - G (pts x n))‖
        ≤ (N : ℝ)⁻¹ * (N * (δ / 4)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = δ / 4 := by field_simp
  have b3 : ‖(∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t‖ ≤ δ / 4 := by
    rw [← integral_sub (integrable_of_continuous _ G.continuous)
      (integrable_of_continuous _ F.continuous)]
    have hb : ‖∫ t : AddCircle (1 : ℝ), (G t - F t)‖
        ≤ (δ / 4) * (volume (univ : Set (AddCircle (1 : ℝ)))).toReal := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards with t
      rw [← norm_neg]
      simpa using hd t
    rw [AddCircle.measure_univ] at hb
    simpa using hb
  have b2 := (hN₁ N (le_trans (le_max_left _ _) hN)).le
  rw [Complex.dist_eq] at b2 ⊢
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - ∫ t : AddCircle (1 : ℝ), F t‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n) - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n)‖
        + ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n) - ∫ t : AddCircle (1 : ℝ), G t‖
        + ‖(∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t‖ := by
        have := norm_add₃_le
          (a := (N : ℂ)⁻¹ * ∑ n ∈ range N, F (pts x n)
            - (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n))
          (b := (N : ℂ)⁻¹ * ∑ n ∈ range N, G (pts x n) - ∫ t : AddCircle (1 : ℝ), G t)
          (c := (∫ t : AddCircle (1 : ℝ), G t) - ∫ t : AddCircle (1 : ℝ), F t)
        simpa using this
    _ ≤ δ / 4 + δ / 4 + δ / 4 := by gcongr
    _ < δ := by linarith

/-- Trigonometric polynomials are uniformly dense in the continuous functions on the circle. -/

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

import Mathlib
/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem tendsto_average_of_monotone {x : ℕ → ℝ} (hx : UniformlyDistributedMod1 x)
    {g : ℝ → ℝ} (hg : Monotone g) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I : ℝ := ∫ t in (0:ℝ)..1, g t
  obtain ⟨K0, hK0⟩ := exists_nat_gt (4 * (g 1 - g 0) / ε)
  obtain ⟨K, hK, hKgt⟩ : ∃ K : ℕ, 0 < K ∧ 4 * (g 1 - g 0) / ε < K :=
    ⟨K0 + 1, Nat.succ_pos _, lt_of_lt_of_le hK0 (by exact_mod_cast Nat.le_succ K0)⟩
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hDK : (g 1 - g 0) / K < ε / 4 := by
    have h1 : 4 * (g 1 - g 0) < K * ε := (div_lt_iff₀ hε).1 hKgt
    rw [div_lt_iff₀ hKpos]
    linarith
  -- the normalized counting functions converge to `1 / K`
  have hcount : ∀ i ∈ Finset.range K,
      Tendsto (fun N : ℕ => (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) / N) atTop
        (𝓝 (1/(K:ℝ))) := by
    intro i hi
    have hiK : (i : ℝ) + 1 ≤ K := by
      have h := Finset.mem_range.1 hi
      exact_mod_cast Nat.succ_le_of_lt h
    have h := hx ((i:ℝ)/K) (((i:ℝ)+1)/K) (by positivity)
      (by rw [div_le_div_iff_of_pos_right hKpos]; linarith)
      (by rw [div_le_one hKpos]; linarith)
    have heq : ((i:ℝ)+1)/K - (i:ℝ)/K = 1/K := by rw [div_sub_div_same]; norm_num
    rwa [heq] at h
  set L : ℝ := ∑ i ∈ Finset.range K, (1/(K:ℝ)) * g ((i:ℝ)/K) with hLdef
  set U : ℝ := ∑ i ∈ Finset.range K, (1/(K:ℝ)) * g (((i:ℝ)+1)/K) with hUdef
  have hLN : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)) atTop (𝓝 L) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).mul_const _)
  have hUN : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K)) atTop (𝓝 U) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).mul_const _)
  -- the two Riemann sums bracket the integral, and differ by `(g 1 - g 0) / K`
  have hLI : L ≤ I := by
    calc L = ∑ i ∈ Finset.range K, g ((i:ℝ)/K) / K :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ I := lower_sum_le_integral hg hK
  have hIU : I ≤ U := by
    calc I ≤ ∑ i ∈ Finset.range K, g (((i:ℝ)+1)/K) / K := integral_le_upper_sum hg hK
      _ = U := Finset.sum_congr rfl (fun i _ => by ring)
  have hUsubL : U - L = (g 1 - g 0) / K := by
    have hFsum : ∑ i ∈ Finset.range K,
        (g (((i + 1 : ℕ) : ℝ)/(K:ℝ)) - g ((i : ℝ)/K)) = g 1 - g 0 := by
      have h := Finset.sum_range_sub (fun i : ℕ => g ((i : ℝ)/K)) K
      simpa [div_self (ne_of_gt hKpos)] using h
    have hstep : U - L = ∑ i ∈ Finset.range K,
        (1/(K:ℝ)) * (g (((i + 1 : ℕ) : ℝ)/(K:ℝ)) - g ((i : ℝ)/K)) := by
      rw [hUdef, hLdef, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [hstep, ← Finset.mul_sum, hFsum]
    ring
  -- combine everything
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 hLN) (ε/4) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 hUN) (ε/4) (by linarith)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ 1) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hb1 := hN1 N (le_trans (le_trans (le_max_left N1 N2) (le_max_left _ 1)) hN)
  have hb2 := hN2 N (le_trans (le_trans (le_max_right N1 N2) (le_max_left _ 1)) hN)
  rw [Real.dist_eq, abs_lt] at hb1 hb2
  have hsplitL : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)
      = (∑ i ∈ Finset.range K,
          (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) * g ((i:ℝ)/K)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsplitU : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K)
      = (∑ i ∈ Finset.range K,
          (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) * g (((i:ℝ)+1)/K)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hlow : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    rw [hsplitL, div_le_div_iff_of_pos_right hNR]
    exact sum_lower_bound hg x hK N
  have hup : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K) := by
    rw [hsplitU, div_le_div_iff_of_pos_right hNR]
    exact sum_upper_bound hg x hK N
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- Version of `tendsto_average_of_monotone` for functions monotone only on `[0,1]`. -/

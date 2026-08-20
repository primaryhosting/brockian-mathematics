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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/

lemma tendsto_average_of_monotoneOn {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  set I : ℝ := ∫ t in (0 : ℝ)..1, g t with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hD : 0 ≤ g 1 - g 0 :=
    sub_nonneg.2 (hg (by norm_num) (by norm_num) zero_le_one)
  obtain ⟨k, hkgt⟩ := exists_nat_gt (2 * (g 1 - g 0) / ε)
  have hknn : (0 : ℝ) ≤ 2 * (g 1 - g 0) / ε := by positivity
  have hk0 : 0 < k := by
    by_contra h
    push_neg at h
    interval_cases k
    · simp at hkgt; linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkD : (g 1 - g 0) / k < ε / 2 := by
    rw [div_lt_iff₀ hε] at hkgt
    rw [div_lt_iff₀ hk']
    linarith
  set L : ℝ := ∑ i ∈ Finset.range k, g ((i : ℝ) / k) / k with hLdef
  set U : ℝ := ∑ i ∈ Finset.range k, g (((i : ℝ) + 1) / k) / k with hUdef
  have hLI : L ≤ I := lower_sum_le_integral hg hk0
  have hIU : I ≤ U := integral_le_upper_sum hg hk0
  have hUL : U - L = (g 1 - g 0) / k := upper_sub_lower hk0
  have hlow := tendsto_weighted_density hx hk0 (fun i : ℕ => g ((i : ℝ) / k))
  have hupp := tendsto_weighted_density hx hk0 (fun i : ℕ => g (((i : ℝ) + 1) / k))
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hupp (ε / 4) (by linarith)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hl := hN1 N hNN1
  have hu := hN2 N hNN2
  rw [Real.dist_eq, abs_lt] at hl hu
  have hlow_le : (∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * g ((i : ℝ) / k)) / N
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    gcongr
    exact lower_sum_le hg x hk0 N
  have hle_upp : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ (∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)
          * g (((i : ℝ) + 1) / k)) / N := by
    gcongr
    exact le_upper_sum hg x hk0 N
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hl.1, hu.2]
  · linarith [hl.1, hu.2]

/-- **Config count density for functions of bounded variation.**
If the configuration counts of `x` have the expected densities on all windows
(`EquidistributedMod1`), then the Birkhoff averages along `x` of any function of bounded
variation on `[0,1]` converge to its integral. -/

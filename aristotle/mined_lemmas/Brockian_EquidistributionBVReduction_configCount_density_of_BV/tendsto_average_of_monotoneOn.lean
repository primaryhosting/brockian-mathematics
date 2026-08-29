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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

theorem tendsto_average_of_monotoneOn (hx : EquidistributedMod1 x)
    (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  classical
  set I := ∫ t in (0:ℝ)..1, g t with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hg01 : g 0 ≤ g 1 := hg (by norm_num) (by norm_num) (by norm_num)
  -- choose a fine enough partition
  obtain ⟨K, hK1, hKε⟩ : ∃ K : ℕ, 0 < K ∧ (g 1 - g 0) / K < ε / 4 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (4 * (g 1 - g 0) / ε))
    have h1 : (1:ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
    have h2 : 4 * (g 1 - g 0) / ε < K := lt_of_le_of_lt (le_max_right _ _) hK
    have hK' : (0:ℝ) < K := by linarith
    refine ⟨K, by exact_mod_cast hK', ?_⟩
    rw [div_lt_div_iff₀ hK' (by norm_num : (0:ℝ) < 4)]
    rw [div_lt_iff₀ hε] at h2
    linarith
  have hK' : (0:ℝ) < K := by exact_mod_cast hK1
  set L := ∑ j ∈ Finset.range K, (1 / (K:ℝ)) * g ((j:ℝ)/K) with hL
  set U := ∑ j ∈ Finset.range K, (1 / (K:ℝ)) * g (((j:ℝ)+1)/K) with hU
  have hLI : L ≤ I := lower_riemann_le_integral hg hK1
  have hIU : I ≤ U := integral_le_upper_riemann hg hK1
  have hUL : U - L = (g 1 - g 0) / K := by
    rw [hU, hL, ← Finset.sum_sub_distrib]
    have : ∀ j ∈ Finset.range K,
        (1 / (K:ℝ)) * g (((j:ℝ)+1)/K) - (1 / (K:ℝ)) * g ((j:ℝ)/K)
          = (1 / (K:ℝ)) * ((fun m : ℕ => g ((m:ℝ)/K)) (j+1) - (fun m : ℕ => g ((m:ℝ)/K)) j) := by
      intro j _
      simp only
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_range_sub
      (fun m : ℕ => g ((m:ℝ)/K))]
    simp only [Nat.cast_zero, zero_div]
    rw [div_self hK'.ne']
    ring
  -- the two empirical Riemann sums converge
  have hSL := tendsto_riemann_sums (x := x) hx hK1 (fun j => g ((j:ℝ)/K))
  have hSU := tendsto_riemann_sums (x := x) hx hK1 (fun j => g (((j:ℝ)+1)/K))
  rw [Metric.tendsto_atTop] at hSL hSU
  obtain ⟨N₁, hN₁⟩ := hSL (ε/4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hSU (ε/4) (by linarith)
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  -- sandwich the orbit average
  have hlow : ∑ j ∈ Finset.range K,
      ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * g ((j:ℝ)/K)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    have heq : ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * g ((j:ℝ)/K)
        = (∑ j ∈ Finset.range K,
          (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) * g ((j:ℝ)/K)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [heq]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (sum_fiber_lower x hg hK1 N)
  have hhigh : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range K,
      ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N)
        * g (((j:ℝ)+1)/K) := by
    have heq : ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N)
          * g (((j:ℝ)+1)/K)
        = (∑ j ∈ Finset.range K,
          (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ)
            * g (((j:ℝ)+1)/K)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [heq]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (sum_fiber_upper x hg hK1 N)
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith; linarith]

end Monotone

variable {x : ℕ → ℝ} {f : ℝ → ℝ}

/-- Koksma-type reduction: for a function of bounded variation on `[0,1]`, the Cesàro
averages along an equidistributed sequence converge to the integral. -/

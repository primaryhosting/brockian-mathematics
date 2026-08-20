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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/

theorem monotoneOn_avg_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  refine tendsto_of_eventually_abs_sub_le (fun ε hε => ?_)
  set I : ℝ := ∫ t in (0:ℝ)..1, f t with hI
  set V : ℝ := f 1 - f 0 with hV
  have hV0 : 0 ≤ V := sub_nonneg.2 (hf ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (4*(V+1)/ε)
  have hpos' : 0 < 4*(V+1)/ε := by positivity
  have hmpos : (0:ℝ) < m := lt_trans hpos' hmgt
  have hmpos0 : 0 < m := by exact_mod_cast hmpos
  have hVm : V/m ≤ ε/4 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    rw [div_lt_iff₀ hε] at hmgt
    nlinarith
  set SU : ℝ := ∑ i ∈ range m, f (((i:ℝ)+1)/m) / m with hSU
  set SL : ℝ := ∑ i ∈ range m, f ((i:ℝ)/m) / m with hSL
  have hdiff : SU - SL = V/m := riemann_diff f hmpos0
  have hSLI : SL ≤ I := riemann_lower hf hmpos0
  have hISU : I ≤ SU := riemann_upper hf hmpos0
  set Uf : ℕ → ℝ := fun N => (∑ n ∈ range N, ∑ i ∈ range m,
      f (((i:ℝ)+1)/m) * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0))/(N:ℝ)
    with hUf
  set Lf : ℕ → ℝ := fun N => (∑ n ∈ range N, ∑ i ∈ range m,
      f ((i:ℝ)/m) * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0))/(N:ℝ)
    with hLf
  have hUlim : Tendsto Uf atTop (𝓝 SU) := avg_step_tendsto hx hmpos0 _
  have hLlim : Tendsto Lf atTop (𝓝 SL) := avg_step_tendsto hx hmpos0 _
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hUlim (ε/4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hLlim (ε/4) (by positivity)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  have hUN := hN₁ N (le_trans (le_max_left _ _) hN)
  have hLN := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hUN hLN
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hup : (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ) ≤ Uf N := by
    rw [hUf]
    exact div_le_div_of_nonneg_right
      (sum_le_sum fun n _ =>
        le_step_upper hf hmpos0 (Int.fract_nonneg _) (Int.fract_lt_one _)) hNnn
  have hlo : Lf N ≤ (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ) := by
    rw [hLf]
    exact div_le_div_of_nonneg_right
      (sum_le_sum fun n _ =>
        step_lower_le hf hmpos0 (Int.fract_nonneg _) (Int.fract_lt_one _)) hNnn
  rw [abs_le]
  exact ⟨by linarith [hLN.1, hdiff, hSLI, hVm], by linarith [hUN.2, hdiff, hISU, hVm]⟩

/-! ### Step 5: the bounded-variation reduction -/

/-- **Equidistribution reduction for functions of bounded variation.** -/

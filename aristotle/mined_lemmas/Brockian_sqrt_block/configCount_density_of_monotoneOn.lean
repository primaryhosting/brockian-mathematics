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

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/

theorem configCount_density_of_monotoneOn (hx : Equidistributed x)
    (hg : MonotoneOn g (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount g x N / N) atTop (nhds (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m0, hm0⟩ := exists_nat_gt ((g 1 - g 0) * 2 / ε)
  set m : ℕ := m0 + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos m0
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmgt : (g 1 - g 0) * 2 / ε < m := by
    refine lt_of_lt_of_le hm0 ?_
    rw [hmdef]
    push_cast
    linarith
  have hgap : (g 1 - g 0) / m < ε / 2 := by
    rw [div_lt_div_iff₀ hm' (by norm_num)]
    rw [div_lt_iff₀ hε] at hmgt
    linarith
  set Lo : ℝ := ∑ i ∈ Finset.range m, g ((i : ℝ) / m) / m
  set Hi : ℝ := ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m
  have hLoI : Lo ≤ ∫ t in (0:ℝ)..1, g t := lower_sum_le_integral hg hm
  have hIHi : (∫ t in (0:ℝ)..1, g t) ≤ Hi := integral_le_upper_sum hg hm
  have hHL : Hi - Lo = (g 1 - g 0) / m := upper_sub_lower g hm
  have hA := tendsto_step_average (x := x) hx (fun i => g ((i : ℝ) / m)) hm
  have hB := tendsto_step_average (x := x) hx (fun i => g (((i : ℝ) + 1) / m)) hm
  rw [Metric.tendsto_atTop] at hA hB
  obtain ⟨N1, hN1⟩ := hA (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hB (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hA' := hN1 N (le_trans (le_max_left _ _) hN)
  have hB' := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hA' hB'
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow : (∑ i ∈ Finset.range m,
      g ((i : ℝ) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N
      ≤ configCount g x N / N := by
    gcongr
    exact sum_lower_le_configCount hg hm N
  have hupp : configCount g x N / N ≤ (∑ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N := by
    gcongr
    exact configCount_le_sum_upper hg hm N
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Monotone

/-- **Bounded-variation reduction for equidistributed sequences.**
If `x` is equidistributed mod one and the weight `w` has bounded variation on `[0, 1]`, then
the weighted configuration counts `∑_{n < N} w (fract (x n))` have density `∫₀¹ w`. -/

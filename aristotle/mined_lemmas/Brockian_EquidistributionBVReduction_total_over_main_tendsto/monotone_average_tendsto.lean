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
# Reduction of equidistribution statements to functions of bounded variation

This file develops the classical "bounded variation reduction" step in equidistribution
theory: if a sequence `x : ℕ → ℝ` taking values in `[0, 1)` is equidistributed (i.e. the
proportion of the first `N` terms lying below `c` tends to `c` for every `c ∈ [0,1]`), then
for every function `f` of bounded variation on `[0,1]` the averages
`(1/N) * ∑_{n < N} f (x n)` converge to `∫₀¹ f`.

The final statement `total_over_main_tendsto` says that the *total* sum `∑_{n < N} f (x n)`
divided by the *main term* `N * ∫₀¹ f` tends to `1`, whenever the integral is nonzero.
-/

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` with `x n < c`. -/

theorem monotone_average_tendsto (hf : MonotoneOn f (Set.Icc (0:ℝ) 1))
    (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (heq : Equidistributed x) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m0, hm0⟩ := exists_nat_gt (2 * (f 1 - f 0) / ε)
  set m : ℕ := m0 + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos _
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hmε : (f 1 - f 0) / m < ε / 2 := by
    rw [div_lt_iff₀ hm']
    have hlt : 2 * (f 1 - f 0) / ε < m := by
      have : (m0 : ℝ) < m := by
        rw [hmdef]; push_cast; linarith
      linarith
    have := (div_lt_iff₀ hε).mp hlt
    linarith
  set J : ℝ := ∫ t in (0:ℝ)..1, f t with hJdef
  set L : ℝ := ∑ k ∈ Finset.range m, f (k / m) * (1 / m) with hLdef
  set U : ℝ := ∑ k ∈ Finset.range m, f (((k : ℝ) + 1) / m) * (1 / m) with hUdef
  have hUL : U - L = (f 1 - f 0) / m := upper_sub_lower_riemann hm
  have hLJ : L ≤ J := lower_riemann_le_integral hf hm
  have hJU : J ≤ U := integral_le_upper_riemann hf hm
  set LN : ℕ → ℝ := fun N => ∑ k ∈ Finset.range m,
    f (k / m) * ((countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ) / N) with hLNdef
  set UN : ℕ → ℝ := fun N => ∑ k ∈ Finset.range m,
    f (((k : ℝ) + 1) / m) * ((countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ) / N) with hUNdef
  have hcell : ∀ k < m, Tendsto
      (fun N : ℕ => (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ) / N) atTop (𝓝 (1 / m)) := by
    intro k hk
    have hb : (((k : ℝ) + 1) / m) ∈ Set.Icc (0:ℝ) 1 := by
      have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) / m ∈ Set.Icc (0:ℝ) 1 := partition_mem m hm hk
      push_cast at h2
      exact h2
    have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by gcongr; linarith
    have h := tendsto_countIco heq (partition_mem m hm hk.le) hb hle
    have hlen : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by
      field_simp
      ring
    rwa [hlen] at h
  have htL : Tendsto LN atTop (𝓝 L) := by
    rw [hLNdef, hLdef]
    exact tendsto_finset_sum _ fun k hk =>
      (hcell k (Finset.mem_range.mp hk)).const_mul (f (k / m))
  have htU : Tendsto UN atTop (𝓝 U) := by
    rw [hUNdef, hUdef]
    exact tendsto_finset_sum _ fun k hk =>
      (hcell k (Finset.mem_range.mp hk)).const_mul (f (((k : ℝ) + 1) / m))
  have hlow : ∀ N : ℕ, 0 < N → LN N ≤ (∑ n ∈ Finset.range N, f (x n)) / N := by
    intro N hN
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hrw : LN N
        = (∑ k ∈ Finset.range m,
            f (k / m) * (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ)) / N := by
      rw [hLNdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrw]
    gcongr
    exact lower_sum_le hf hx hm N
  have hupp : ∀ N : ℕ, 0 < N → (∑ n ∈ Finset.range N, f (x n)) / N ≤ UN N := by
    intro N hN
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hrw : UN N
        = (∑ k ∈ Finset.range m,
            f (((k : ℝ) + 1) / m) * (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ)) / N := by
      rw [hUNdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrw]
    gcongr
    exact le_upper_sum hf hx hm N
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp htL (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp htU (ε / 4) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hN)
  have hL1 : |LN N - L| < ε / 4 := by
    have := hN₁ N (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hN)
    rwa [Real.dist_eq] at this
  have hU1 : |UN N - U| < ε / 4 := by
    have := hN₂ N (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hN)
    rwa [Real.dist_eq] at this
  rw [abs_lt] at hL1 hU1
  rw [Real.dist_eq, abs_sub_lt_iff]
  have hb1 := hlow N hNpos
  have hb2 := hupp N hNpos
  constructor <;> linarith

end Monotone

section BoundedVariation

variable {f : ℝ → ℝ} {x : ℕ → ℝ}

/-- Averages of a function of bounded variation along an equidistributed sequence converge to
its integral. -/

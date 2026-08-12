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
noncomputable def countLt (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => x n < c)).card

/-- The number of indices `n < N` with `x n ∈ [a, b)`. -/
noncomputable def countIco (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => a ≤ x n ∧ x n < b)).card

/-- A sequence is equidistributed in `[0,1]` if for every `c ∈ [0,1]` the proportion of the
first `N` terms that are `< c` tends to `c`. -/
def Equidistributed (x : ℕ → ℝ) : Prop :=
  ∀ c ∈ Set.Icc (0 : ℝ) 1,
    Tendsto (fun N : ℕ => (countLt x N c : ℝ) / N) atTop (𝓝 c)

/-- Sanity check: the equidistribution hypothesis has genuine content, e.g. a constant
sequence is not equidistributed. -/
lemma not_equidistributed_const : ¬ Equidistributed (fun _ : ℕ => (0:ℝ)) := by
  intro h
  have h2 := h (1/2) (by constructor <;> norm_num)
  have heq1 : ∀ᶠ N : ℕ in atTop, (countLt (fun _ : ℕ => (0:ℝ)) N (1/2) : ℝ) / N = 1 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcount : countLt (fun _ : ℕ => (0:ℝ)) N (1/2) = N := by
      unfold countLt
      rw [Finset.filter_true_of_mem (fun n _ => by norm_num), Finset.card_range]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hcount, div_self hN']
  have hcontra := tendsto_nhds_unique (h2.congr' heq1) tendsto_const_nhds
  norm_num at hcontra

section Counting

variable {x : ℕ → ℝ} {N : ℕ} {a b : ℝ}

lemma countLt_add_countIco (hab : a ≤ b) :
    countLt x N a + countIco x N a b = countLt x N b := by
  classical
  have h1 : ((Finset.range N).filter (fun n => x n < b)).filter (fun n => x n < a)
      = (Finset.range N).filter (fun n => x n < a) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_of_lt_of_le h.2 hab⟩, h.2⟩⟩
  have h2 : ((Finset.range N).filter (fun n => x n < b)).filter (fun n => ¬ (x n < a))
      = (Finset.range N).filter (fun n => a ≤ x n ∧ x n < b) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    tauto
  unfold countLt countIco
  rw [← h1, ← h2]
  exact Finset.card_filter_add_card_filter_not _

lemma tendsto_countIco (heq : Equidistributed x) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (countIco x N a b : ℝ) / N) atTop (𝓝 (b - a)) := by
  have key : ∀ N : ℕ, (countIco x N a b : ℝ) / N
      = (countLt x N b : ℝ) / N - (countLt x N a : ℝ) / N := by
    intro N
    have h := countLt_add_countIco (x := x) (N := N) hab
    have h' : (countLt x N a : ℝ) + (countIco x N a b : ℝ) = (countLt x N b : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    rw [div_sub_div_same]
    congr 1
    linarith
  simp only [key]
  exact (heq b hb).sub (heq a ha)

end Counting

section Monotone

variable {f : ℝ → ℝ} {x : ℕ → ℝ}

/-- Splitting the first `N` terms according to the cell `[k/m, (k+1)/m)` they belong to. -/
lemma sum_fiber_split (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ k ∈ Finset.range m, ∑ n ∈ (Finset.range N).filter
        (fun n => (k / m : ℝ) ≤ x n ∧ x n < ((k : ℝ) + 1) / m), f (x n)
      = ∑ n ∈ Finset.range N, f (x n) := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hmaps : ∀ n ∈ Finset.range N, ⌊x n * m⌋₊ ∈ Finset.range m := by
    intro n _
    have h0 : 0 ≤ x n * m := mul_nonneg (hx n).1 hm'.le
    have h1 : x n * m < m := by
      have := (hx n).2
      nlinarith
    exact Finset.mem_range.mpr ((Nat.floor_lt h0).mpr h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => f (x n))]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro n _
  have h0 : 0 ≤ x n * m := mul_nonneg (hx n).1 hm'.le
  rw [Nat.floor_eq_iff h0, div_le_iff₀ hm', lt_div_iff₀ hm']

lemma lower_sum_le (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ k ∈ Finset.range m, f (k / m) * (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ)
      ≤ ∑ n ∈ Finset.range N, f (x n) := by
  classical
  rw [← sum_fiber_split (f := f) hx hm N]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hkm : ((k : ℝ) / m) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hm']
      exact_mod_cast hk'.le
  have : (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ)
      = ((Finset.range N).filter
          (fun n => (k / m : ℝ) ≤ x n ∧ x n < ((k : ℝ) + 1) / m)).card := rfl
  rw [this, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum ?_
  intro n hn
  simp only [Finset.mem_filter] at hn
  exact hf hkm ⟨(hx n).1, (hx n).2.le⟩ hn.2.1

lemma le_upper_sum (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (x n)
      ≤ ∑ k ∈ Finset.range m, f (((k : ℝ) + 1) / m) *
          (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ) := by
  classical
  rw [← sum_fiber_split (f := f) hx hm N]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hkm : (((k : ℝ) + 1) / m) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hm']
      have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk'
      linarith
  have : (countIco x N (k / m) (((k : ℝ) + 1) / m) : ℝ)
      = ((Finset.range N).filter
          (fun n => (k / m : ℝ) ≤ x n ∧ x n < ((k : ℝ) + 1) / m)).card := rfl
  rw [this, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum ?_
  intro n hn
  simp only [Finset.mem_filter] at hn
  exact hf ⟨(hx n).1, (hx n).2.le⟩ hkm hn.2.2.le

/-- Auxiliary facts about the uniform partition of `[0,1]` into `m` cells. -/
private lemma partition_mem (m : ℕ) (hm : 0 < m) {k : ℕ} (hk : k ≤ m) :
    ((k : ℝ) / m) ∈ Set.Icc (0:ℝ) 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hm']
  exact_mod_cast hk

private lemma partition_integrable (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) (m : ℕ) (hm : 0 < m)
    {k : ℕ} (hk : k < m) :
    IntervalIntegrable f volume ((k : ℝ) / m) (((k : ℝ) + 1) / m) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by gcongr; linarith
  refine MonotoneOn.intervalIntegrable (hf.mono ?_)
  rw [Set.uIcc_of_le hle]
  have h1 := partition_mem m hm hk.le
  have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) / m ∈ Set.Icc (0:ℝ) 1 := partition_mem m hm hk
  push_cast at h2
  exact Set.Icc_subset_Icc h1.1 h2.2

lemma lower_riemann_le_integral (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Finset.range m, f (k / m) * (1 / m) ≤ ∫ t in (0:ℝ)..1, f t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k < m, IntervalIntegrable f volume ((fun j : ℕ => (j : ℝ) / m) k)
      ((fun j : ℕ => (j : ℝ) / m) (k + 1)) := by
    intro k hk
    have := partition_integrable hf m hm hk
    simpa using this
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero, zero_div] at hsum
  rw [div_self (ne_of_gt hm')] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) / m = ((k : ℝ) + 1) / m := by push_cast; ring
  have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by gcongr; linarith
  have hlen : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by
    field_simp
    ring
  have hconst : f ((k : ℝ) / m) * (1 / m)
      = ∫ _t in ((k : ℝ) / m)..(((k : ℝ) + 1) / m), f ((k : ℝ) / m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen, mul_comm]
  simp only [hcast]
  rw [hconst]
  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
    (partition_integrable hf m hm hk') ?_
  intro t ht
  have h1 := partition_mem m hm hk'.le
  have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) / m ∈ Set.Icc (0:ℝ) 1 := partition_mem m hm hk'
  push_cast at h2
  exact hf h1 ⟨le_trans h1.1 ht.1, le_trans ht.2 h2.2⟩ ht.1

lemma integral_le_upper_riemann (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t) ≤ ∑ k ∈ Finset.range m, f (((k : ℝ) + 1) / m) * (1 / m) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k < m, IntervalIntegrable f volume ((fun j : ℕ => (j : ℝ) / m) k)
      ((fun j : ℕ => (j : ℝ) / m) (k + 1)) := by
    intro k hk
    have := partition_integrable hf m hm hk
    simpa using this
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero, zero_div] at hsum
  rw [div_self (ne_of_gt hm')] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) / m = ((k : ℝ) + 1) / m := by push_cast; ring
  have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by gcongr; linarith
  have hlen : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by
    field_simp
    ring
  have hconst : f (((k : ℝ) + 1) / m) * (1 / m)
      = ∫ _t in ((k : ℝ) / m)..(((k : ℝ) + 1) / m), f (((k : ℝ) + 1) / m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen, mul_comm]
  simp only [hcast]
  rw [hconst]
  refine intervalIntegral.integral_mono_on hle (partition_integrable hf m hm hk')
    intervalIntegrable_const ?_
  intro t ht
  have h1 := partition_mem m hm hk'.le
  have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) / m ∈ Set.Icc (0:ℝ) 1 := partition_mem m hm hk'
  push_cast at h2
  exact hf ⟨le_trans h1.1 ht.1, le_trans ht.2 h2.2⟩ h2 ht.2

lemma upper_sub_lower_riemann {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ Finset.range m, f (((k : ℝ) + 1) / m) * (1 / m))
      - ∑ k ∈ Finset.range m, f (k / m) * (1 / m) = (f 1 - f 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have : ∀ k ∈ Finset.range m,
      f (((k : ℝ) + 1) / m) * (1 / m) - f (k / m) * (1 / m)
        = ((fun j : ℕ => f ((j : ℝ) / m) * (1 / m)) (k + 1))
          - ((fun j : ℕ => f ((j : ℝ) / m) * (1 / m)) k) := by
    intro k _
    simp only
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / m) * (1 / m))]
  simp only [Nat.cast_zero, zero_div]
  rw [div_self (ne_of_gt hm')]
  ring

/-- Averages of a monotone function along an equidistributed sequence converge to its
integral. -/
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
theorem bv_average_tendsto (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1))
    (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (heq : Equidistributed x) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huicc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le zero_le_one
  have hpi : IntervalIntegrable p volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huicc]; exact hp)
  have hqi : IntervalIntegrable q volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huicc]; exact hq)
  have hInt : (∫ t in (0:ℝ)..1, f t)
      = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [hpq]
    simpa using intervalIntegral.integral_sub hpi hqi
  have hlim := (monotone_average_tendsto hp hx heq).sub (monotone_average_tendsto hq hx heq)
  rw [← hInt] at hlim
  refine hlim.congr fun N => ?_
  rw [hpq]
  simp [Finset.sum_sub_distrib, sub_div]

/-- The total sum `∑_{n < N} f (x n)` is asymptotic to the main term `N * ∫₀¹ f`.

This is unconditional: the bounded-variation reduction it relies on (`bv_average_tendsto`)
is proved in this file, not assumed. -/
theorem total_over_main_tendsto (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1))
    (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (heq : Equidistributed x)
    (hI : (∫ t in (0:ℝ)..1, f t) ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / (N * ∫ t in (0:ℝ)..1, f t))
      atTop (𝓝 1) := by
  have hlim := (bv_average_tendsto hf hx heq).div_const (∫ t in (0:ℝ)..1, f t)
  rw [div_self hI] at hlim
  refine hlim.congr fun N => ?_
  rw [div_div]

end BoundedVariation

end Brockian.EquidistributionBVReduction


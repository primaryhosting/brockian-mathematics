import Brockian.EquidistributionBVReduction

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
# Equidistribution: reduction to bounded–variation test functions

This module contains the "BV reduction" step of an equidistribution argument: the
uniformly distributed sequence of nodes `n / N`, `0 ≤ n < N`, in the unit interval is
tested against a function `f` which is monotone (hence of bounded variation) on `[0, 1]`.

The *total* is the un-normalised sum `∑_{n < N} f (n / N)`, and the *main term* is
`N * ∫_0^1 f`.  The main estimate `abs_total_sub_mainTerm_le` shows that the difference
between the two is bounded by the total variation `f 1 - f 0` of `f`, uniformly in `N`;
consequently the ratio total/main tends to `1`, which is the statement
`total_over_main_tendsto`.
-/

namespace Brockian
namespace EquidistributionBVReduction

open MeasureTheory Filter Topology Set intervalIntegral

/-- The total (un-normalised) sum of the test function `f` over the equidistributed
nodes `n / N`, `0 ≤ n < N`. -/
noncomputable def total (f : ℝ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, f ((n : ℝ) / N)

/-- The main term predicted by equidistribution: `N` times the mean value of `f`. -/
noncomputable def mainTerm (f : ℝ → ℝ) (N : ℕ) : ℝ := (N : ℝ) * ∫ x in (0 : ℝ)..1, f x

section

variable {f : ℝ → ℝ} {N : ℕ}

/-- The nodes `n / N` for `n ≤ N` lie in the unit interval. -/
lemma node_mem_Icc (hN : 0 < N) {n : ℕ} (hn : n ≤ N) : ((n : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hN']
  exact_mod_cast hn

lemma node_le_node (hN : 0 < N) (n : ℕ) : ((n : ℝ) / N) ≤ ((n + 1 : ℕ) : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  gcongr
  linarith

lemma node_sub_node (hN : 0 < N) (n : ℕ) : ((n + 1 : ℕ) : ℝ) / N - (n : ℝ) / N = 1 / N := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `f` is monotone on the `n`-th subinterval `[n/N, (n+1)/N]`. -/
lemma monotoneOn_seg (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) {n : ℕ} (hn : n < N) :
    MonotoneOn f (uIcc ((n : ℝ) / N) (((n + 1 : ℕ) : ℝ) / N)) := by
  refine hf.mono ?_
  rw [uIcc_of_le (node_le_node hN n)]
  exact Icc_subset_Icc (node_mem_Icc hN hn.le).1 (node_mem_Icc hN hn).2

lemma intervalIntegrable_seg (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) {n : ℕ}
    (hn : n < N) : IntervalIntegrable f volume ((n : ℝ) / N) (((n + 1 : ℕ) : ℝ) / N) :=
  (monotoneOn_seg hf hN hn).intervalIntegrable

lemma intervalIntegrable_unit (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    IntervalIntegrable f volume 0 1 := by
  apply MonotoneOn.intervalIntegrable
  rwa [uIcc_of_le (zero_le_one' ℝ)]

/-- Lower Darboux bound on a subinterval. -/
lemma lower_le_integral_seg (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) {n : ℕ}
    (hn : n < N) :
    f ((n : ℝ) / N) / N ≤ ∫ x in ((n : ℝ) / N)..(((n + 1 : ℕ) : ℝ) / N), f x := by
  have hle := node_le_node hN n
  have hconst : (∫ _x in ((n : ℝ) / N)..(((n + 1 : ℕ) : ℝ) / N), f ((n : ℝ) / N))
      = f ((n : ℝ) / N) / N := by
    rw [intervalIntegral.integral_const, node_sub_node hN n]
    simp [div_eq_inv_mul]
  rw [← hconst]
  refine intervalIntegral.integral_mono_on hle intervalIntegral.intervalIntegrable_const
    (intervalIntegrable_seg hf hN hn) ?_
  intro x hx
  refine hf (node_mem_Icc hN hn.le) ⟨le_trans (node_mem_Icc hN hn.le).1 hx.1,
    le_trans hx.2 (node_mem_Icc hN hn).2⟩ hx.1

/-- Upper Darboux bound on a subinterval. -/
lemma integral_seg_le_upper (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) {n : ℕ}
    (hn : n < N) :
    (∫ x in ((n : ℝ) / N)..(((n + 1 : ℕ) : ℝ) / N), f x) ≤ f (((n + 1 : ℕ) : ℝ) / N) / N := by
  have hle := node_le_node hN n
  have hconst : (∫ _x in ((n : ℝ) / N)..(((n + 1 : ℕ) : ℝ) / N), f (((n + 1 : ℕ) : ℝ) / N))
      = f (((n + 1 : ℕ) : ℝ) / N) / N := by
    rw [intervalIntegral.integral_const, node_sub_node hN n]
    simp [div_eq_inv_mul]
  rw [← hconst]
  refine intervalIntegral.integral_mono_on hle (intervalIntegrable_seg hf hN hn)
    intervalIntegral.intervalIntegrable_const ?_
  intro x hx
  refine hf ⟨le_trans (node_mem_Icc hN hn.le).1 hx.1, le_trans hx.2 (node_mem_Icc hN hn).2⟩
    (node_mem_Icc hN hn) hx.2

/-- The subintervals `[n/N, (n+1)/N]` tile `[0, 1]`. -/
lemma sum_integral_seg (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) :
    ∑ n ∈ Finset.range N, (∫ x in ((n : ℝ) / N)..(((n + 1 : ℕ) : ℝ) / N), f x)
      = ∫ x in (0 : ℝ)..1, f x := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := fun k : ℕ => (k : ℝ) / N) (n := N)
    (fun k hk => intervalIntegrable_seg hf hN hk)
  simpa [div_self hN'] using this

/-- Shifting the nodes by one changes the total by the variation `f 1 - f 0`. -/
lemma sum_shift (hN : 0 < N) :
    ∑ n ∈ Finset.range N, f (((n + 1 : ℕ) : ℝ) / N) = total f N + f 1 - f 0 := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h1 : ∑ n ∈ Finset.range (N + 1), f ((n : ℝ) / N)
      = (∑ n ∈ Finset.range N, f (((n + 1 : ℕ) : ℝ) / N)) + f ((0 : ℕ) / N) :=
    Finset.sum_range_succ' (fun n => f ((n : ℝ) / N)) N
  have h2 : ∑ n ∈ Finset.range (N + 1), f ((n : ℝ) / N)
      = (∑ n ∈ Finset.range N, f ((n : ℝ) / N)) + f ((N : ℝ) / N) :=
    Finset.sum_range_succ (fun n => f ((n : ℝ) / N)) N
  rw [h1] at h2
  simp only [Nat.cast_zero, zero_div, div_self hN'] at h2
  unfold total
  linarith

lemma total_le_mainTerm (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) :
    total f N ≤ mainTerm f N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : total f N / N ≤ ∫ x in (0 : ℝ)..1, f x := by
    rw [← sum_integral_seg hf hN, total, Finset.sum_div]
    exact Finset.sum_le_sum fun n hn =>
      lower_le_integral_seg hf hN (Finset.mem_range.mp hn)
  rw [div_le_iff₀ hN'] at key
  rw [mainTerm, mul_comm]
  exact key

lemma mainTerm_le_total_add (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) :
    mainTerm f N ≤ total f N + (f 1 - f 0) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (∫ x in (0 : ℝ)..1, f x) ≤ (total f N + f 1 - f 0) / N := by
    rw [← sum_integral_seg hf hN, ← sum_shift (f := f) hN, Finset.sum_div]
    exact Finset.sum_le_sum fun n hn =>
      integral_seg_le_upper hf hN (Finset.mem_range.mp hn)
  rw [le_div_iff₀ hN'] at key
  rw [mainTerm, mul_comm]
  linarith

/-- **Key estimate.** The total differs from the main term by at most the total variation
of the test function, uniformly in `N`. -/
lemma abs_total_sub_mainTerm_le (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (hN : 0 < N) :
    |total f N - mainTerm f N| ≤ f 1 - f 0 := by
  have hvar : f 0 ≤ f 1 := hf (by norm_num) (by norm_num) zero_le_one
  rw [abs_le]
  constructor
  · linarith [mainTerm_le_total_add hf hN]
  · linarith [total_le_mainTerm hf hN]

end

/-- **Equidistribution, BV reduction.**  If the test function `f` is monotone on `[0,1]`
and has nonzero mean, then the total sum over the equidistributed nodes `n/N`, `n < N`,
is asymptotic to the main term `N * ∫_0^1 f`. -/
theorem total_over_main_tendsto {f : ℝ → ℝ} (hf : MonotoneOn f (Icc (0 : ℝ) 1))
    (hI : (∫ x in (0 : ℝ)..1, f x) ≠ 0) :
    Tendsto (fun N : ℕ => total f N / mainTerm f N) atTop (𝓝 1) := by
  set I : ℝ := ∫ x in (0 : ℝ)..1, f x with hIdef
  have hIpos : 0 < |I| := abs_pos.mpr hI
  have hg : Tendsto (fun N : ℕ => (f 1 - f 0) / |I| * (1 / (N : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h0.const_mul ((f 1 - f 0) / |I|)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖total f N / mainTerm f N - 1‖ ≤ (f 1 - f 0) / |I| * (1 / (N : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hmain : mainTerm f N = (N : ℝ) * I := rfl
    have hmain0 : mainTerm f N ≠ 0 := by
      rw [hmain]; exact mul_ne_zero (ne_of_gt hN') hI
    have habs : |mainTerm f N| = (N : ℝ) * |I| := by
      rw [hmain, abs_mul, abs_of_pos hN']
    have hsub : total f N / mainTerm f N - 1 = (total f N - mainTerm f N) / mainTerm f N := by
      field_simp
    rw [Real.norm_eq_abs, hsub, abs_div, habs, div_le_iff₀ (by positivity)]
    have h1 : |total f N - mainTerm f N| ≤ f 1 - f 0 := abs_total_sub_mainTerm_le hf hN
    have : (f 1 - f 0) / |I| * (1 / (N : ℝ)) * ((N : ℝ) * |I|) = f 1 - f 0 := by
      field_simp
    rw [this]
    exact h1
  have := squeeze_zero_norm' hbound hg
  have h2 := this.add_const 1
  simpa using h2

/-- Sanity check that the hypotheses of `total_over_main_tendsto` are satisfiable:
they hold for the identity test function. -/
example :
    Tendsto (fun N : ℕ => total (fun x => x) N / mainTerm (fun x => x) N) atTop (𝓝 1) :=
  total_over_main_tendsto (fun _ _ _ _ h => h) (by rw [integral_id]; norm_num)

end EquidistributionBVReduction
end Brockian


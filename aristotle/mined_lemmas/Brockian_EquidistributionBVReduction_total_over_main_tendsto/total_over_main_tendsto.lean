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


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

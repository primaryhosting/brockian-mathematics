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

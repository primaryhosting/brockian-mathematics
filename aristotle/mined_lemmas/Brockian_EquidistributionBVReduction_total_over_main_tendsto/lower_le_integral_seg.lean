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

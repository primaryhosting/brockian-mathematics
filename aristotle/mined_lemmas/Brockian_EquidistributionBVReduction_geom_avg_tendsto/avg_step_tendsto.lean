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

theorem avg_step_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {m : ℕ} (hm : 0 < m)
    (cf : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ∑ i ∈ range m,
        cf i * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)) / (N:ℝ))
      atTop (𝓝 (∑ i ∈ range m, cf i / m)) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have key : ∀ N : ℕ, (∑ n ∈ range N, ∑ i ∈ range m,
      cf i * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)) / (N:ℝ)
      = ∑ i ∈ range m, cf i *
        ((((range N).filter fun n =>
            Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)).card : ℝ)/(N:ℝ)) := by
    intro N
    rw [Finset.sum_comm, Finset.sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, card_filter]
    push_cast
    rw [mul_div_assoc]
  simp only [key]
  have heq : ∑ i ∈ range m, cf i / m = ∑ i ∈ range m, cf i * (((i:ℝ)+1)/m - (i:ℝ)/m) := by
    refine sum_congr rfl fun i _ => ?_
    rw [show ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m by ring, mul_one_div]
  rw [heq]
  refine tendsto_finset_sum _ fun i hi => ?_
  refine Tendsto.const_mul _ ?_
  refine hx ((i:ℝ)/m) (((i:ℝ)+1)/m) (by positivity) (by gcongr; linarith) ?_
  rw [div_le_one hmpos]
  have h1 : i < m := mem_range.1 hi
  have : (i:ℝ) + 1 ≤ m := by exact_mod_cast h1
  linarith

/-- The upper grid step function dominates a monotone function. -/

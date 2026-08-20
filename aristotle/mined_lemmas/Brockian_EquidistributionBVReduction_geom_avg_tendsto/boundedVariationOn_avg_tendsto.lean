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

theorem boundedVariationOn_avg_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le zero_le_one]
  have hqi : IntervalIntegrable q volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le zero_le_one]
  have hInt : (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [← intervalIntegral.integral_sub hpi hqi]
    congr 1
  rw [hInt]
  refine ((monotoneOn_avg_tendsto hx hp).sub (monotoneOn_avg_tendsto hx hq)).congr (fun N => ?_)
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by simp [hpq]

/-- **Main theorem.** For an irrational `α` and a function `f` of bounded variation on `[0,1]`
with nonzero integral, the total sum `∑_{n < N} f (fract (nα))` divided by the main term
`N · ∫₀¹ f` tends to `1`. -/

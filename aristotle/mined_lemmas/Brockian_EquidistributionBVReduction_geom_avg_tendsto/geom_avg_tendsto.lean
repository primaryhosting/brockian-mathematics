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

theorem geom_avg_tendsto (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, z ^ n) / (N : ℂ)) atTop (𝓝 0) := by
  have hzn : (0:ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  have hS : ∀ N : ℕ, ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    rw [geom_sum_eq hz1, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖(z:ℂ) ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hz]; norm_num
  refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖z - 1‖))
  rw [norm_div, Complex.norm_natCast]
  gcongr
  exact hS N

/-- The Fourier character evaluated along the orbit is a geometric sequence. -/

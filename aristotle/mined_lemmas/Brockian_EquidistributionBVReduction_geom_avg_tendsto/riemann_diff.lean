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

theorem riemann_diff (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ range m, f (((i:ℝ)+1)/m) / m) - (∑ i ∈ range m, f ((i:ℝ)/m) / m)
      = (f 1 - f 0)/m := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have : ∀ i ∈ range m, f (((i:ℝ)+1)/m) / m - f ((i:ℝ)/m) / m
      = (fun j : ℕ => f ((j:ℝ)/m)/m) (i+1) - (fun j : ℕ => f ((j:ℝ)/m)/m) i := by
    intro i _
    dsimp only
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j : ℕ => f ((j:ℝ)/m)/m)]
  rw [Nat.cast_zero, zero_div]
  have h1 : (m:ℝ)/m = 1 := by field_simp
  rw [h1]
  ring

/-- **Equidistribution reduction for monotone functions.** If `x` is equidistributed mod one and
`f` is monotone on `[0,1]`, then the Cesàro averages of `f` along the fractional parts of `x`
converge to `∫₀¹ f`. -/

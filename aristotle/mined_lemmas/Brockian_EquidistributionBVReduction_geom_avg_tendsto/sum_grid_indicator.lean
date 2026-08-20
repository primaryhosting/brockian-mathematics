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

theorem sum_grid_indicator {m : ℕ} (hm : 0 < m) (cf : ℕ → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∑ i ∈ range m, cf i * (if t ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)
      = cf ⌊(m:ℝ)*t⌋₊ := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hlt : ⌊(m:ℝ)*t⌋₊ < m := by
    refine (Nat.floor_lt' (by omega)).2 ?_
    calc (m:ℝ)*t < m*1 := by exact mul_lt_mul_of_pos_left ht1 hmpos
      _ = m := by ring
  rw [Finset.sum_eq_single ⌊(m:ℝ)*t⌋₊]
  · rw [if_pos ((grid_floor_iff hm ht0 _).2 rfl), mul_one]
  · intro j _ hj
    rw [if_neg (fun hmem => hj ((grid_floor_iff hm ht0 j).1 hmem).symm), mul_zero]
  · intro h
    exact absurd (mem_range.2 hlt) h

/-- Averages of grid step functions along an equidistributed sequence. -/

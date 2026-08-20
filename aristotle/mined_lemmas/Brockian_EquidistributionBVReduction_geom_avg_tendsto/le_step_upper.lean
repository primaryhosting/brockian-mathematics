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

theorem le_step_upper {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    f t ≤ ∑ i ∈ range m, f (((i:ℝ)+1)/m) * (if t ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_grid_indicator hm (fun i => f (((i:ℝ)+1)/m)) ht0 ht1]
  have hlt : ⌊(m:ℝ)*t⌋₊ < m := by
    refine (Nat.floor_lt' (by omega)).2 ?_
    calc (m:ℝ)*t < m*1 := by exact mul_lt_mul_of_pos_left ht1 hmpos
      _ = m := by ring
  have hle1 : ((⌊(m:ℝ)*t⌋₊ : ℝ) + 1)/m ≤ 1 := by
    rw [div_le_one hmpos]
    have : (⌊(m:ℝ)*t⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    linarith
  have hmem : ((⌊(m:ℝ)*t⌋₊ : ℝ) + 1)/m ∈ Icc (0:ℝ) 1 := ⟨by positivity, hle1⟩
  refine hf ⟨ht0, ht1.le⟩ hmem ?_
  rw [le_div_iff₀ hmpos]
  have := Nat.lt_floor_add_one ((m:ℝ)*t)
  linarith [this]

/-- The lower grid step function is dominated by a monotone function. -/

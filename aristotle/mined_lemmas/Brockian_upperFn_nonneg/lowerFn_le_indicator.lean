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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/

lemma lowerFn_le_indicator (c r d : ℝ) (hd : 0 < d) (x : Circ) :
    lowerFn c r d x ≤ (if dist x ((c : ℝ) : Circ) < r then (1 : ℝ) else 0) := by
  by_cases hx : dist x ((c : ℝ) : Circ) < r
  · rw [if_pos hx]
    simp only [lowerFn, ContinuousMap.coe_mk]
    exact max_le zero_le_one (min_le_left _ _)
  · rw [if_neg hx]
    push_neg at hx
    have h0 : (r - dist x ((c : ℝ) : Circ)) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp only [lowerFn, ContinuousMap.coe_mk]
    exact max_le le_rfl (le_trans (min_le_right _ _) h0)

/-- Upper bound for the volume of a closed arc. -/

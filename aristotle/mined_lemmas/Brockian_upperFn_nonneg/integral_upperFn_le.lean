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

lemma integral_upperFn_le (c r d : ℝ) (hd : 0 < d) (hr : 0 < r) :
    ∫ x : Circ, upperFn c r d x ≤ 2 * (r + d) := by
  have h1 : ∫ x : Circ, upperFn c r d x
      ≤ ∫ x : Circ, (closedBall ((c : ℝ) : Circ) (r + d)).indicator (fun _ => (1 : ℝ)) x :=
    integral_mono (integrable_cont _)
      ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (upperFn_le_indicator c r d hd)
  rw [integral_indicator_closedBall] at h1
  exact h1.trans (volume_closedBall_le _ (by linarith))


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

theorem configCount_over_main_tendsto (a c r : ℝ) (ha : Irrational a) (hr : 0 < r)
    (hr2 : r < 1 / 2) :
    Tendsto (fun N : ℕ => (configCount a c r N : ℝ) / mainTerm r N) atTop (𝓝 1) :=
  configCount_over_main_tendsto_of_equidistributed a c r (equidistributed_of_irrational a ha) hr hr2

end

end EquidistributionBVReduction
end Brockian

import Mathlib

/-!
# Weyl's equidistribution theorem for continuous test functions

For an irrational number `a`, the orbit `n ↦ n • a` on the circle `ℝ/ℤ` is equidistributed:
for every continuous `f : ℝ/ℤ → ℂ` we have

  `(1/N) * ∑_{n < N} f (n • a) → ∫ f`.

The proof is the classical one: the statement holds for the characters `fourier m` by an explicit
geometric-series computation, extends to their linear span by linearity, and then to all
continuous functions by density of the span of characters in the uniform norm
(Stone–Weierstrass, available in Mathlib as `span_fourier_closure_eq_top`).
-/

open MeasureTheory Filter Topology Metric Complex Submodule
open scoped BigOperators Real

namespace Brockian
namespace Weyl

noncomputable section

/-- The circle `ℝ/ℤ`. -/
abbrev Circ := AddCircle (1 : ℝ)

/-- The orbit point `n • a` on the circle `ℝ/ℤ`. -/

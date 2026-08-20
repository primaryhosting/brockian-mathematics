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
# Weyl's equidistribution theorem for irrational rotations

For an irrational number `a`, the fractional parts `{n * a}` are equidistributed in `[0,1)`:
for every subinterval `[u, v) ⊆ [0,1]` the proportion of `n < N` with `Int.fract (n * a) ∈ [u, v)`
tends to `v - u`.

The proof follows Weyl's method:

* `WeylSumsVanish a` is the statement that all non-trivial exponential (Weyl) sums along the
  orbit have vanishing averages;
* `tendsto_orbitAvg_of_weylSumsVanish` is the *conditional* statement that `WeylSumsVanish a`
  implies convergence of Birkhoff averages of continuous functions to their integral;
* `weylSumsVanish_of_irrational` *discharges* that hypothesis for irrational `a` (geometric
  series estimate), making the result unconditional;
* `equidistribution_of_asymptotic_exists` is the final unconditional interval version.
-/

namespace Brockian.Equidistribution

open Filter Topology MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Birkhoff / empirical average of a complex-valued function over the first `N` points of the
orbit of `0` under the rotation by `a` on the circle `ℝ / ℤ`. -/

theorem norm_integral_sub_le (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x ∂AddCircle.haarAddCircle) - ∫ x, g x ∂AddCircle.haarAddCircle‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_of_continuousMap f) (integrable_of_continuousMap g)]
  have hb := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (C := ‖f - g‖) (f := fun x => f x - g x)
    (Filter.Eventually.of_forall fun x => by
      simpa using ContinuousMap.norm_coe_le_norm (f - g) x)
  simpa using hb

/-! ### The conditional statement -/


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

def orbitAvgR (a : ℝ) (f : AddCircle (1 : ℝ) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((n * a : ℝ) : AddCircle (1 : ℝ))

/-- The Weyl criterion hypothesis: all non-trivial exponential sums along the orbit have
averages tending to `0`. -/

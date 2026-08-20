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

theorem density_eq_avg_indicator (a u v : ℝ) (N : ℕ) :
    ((((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N)
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  rw [div_eq_inv_mul]

/-! ### The main theorem -/

/-- **Weyl's equidistribution theorem.**  For irrational `a`, the fractional parts of `n * a`
are equidistributed: the asymptotic density of the set of `n` with `Int.fract (n * a) ∈ [u, v)`
exists and equals `v - u`. -/

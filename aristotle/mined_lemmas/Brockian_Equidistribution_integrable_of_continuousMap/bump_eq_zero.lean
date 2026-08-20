import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem bump_eq_zero (c s ep : ℝ) (hep : 0 < ep) {z : AddCircle (1 : ℝ)}
    (hz : s ≤ ‖z - (c : AddCircle (1 : ℝ))‖) : bump c s ep z = 0 := by
  have h1 : (s - ‖z - (c : AddCircle (1 : ℝ))‖) / ep ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hep.le
  simp only [bump, ContinuousMap.coe_mk]
  rw [max_eq_left h1, min_eq_right zero_le_one]

/-- The integral of `bump c s ep` over the circle, computed as an integral over the interval
of length one centred at `c`. -/

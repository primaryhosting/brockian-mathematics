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

theorem integral_bump_eq (c s ep : ℝ) :
    (∫ z, bump c s ep z) = ∫ t in (c - 1 / 2)..(c + 1 / 2), min 1 (max 0 ((s - |t - c|) / ep)) := by
  rw [← AddCircle.intervalIntegral_preimage 1 (c - 1 / 2), show c - 1 / 2 + 1 = c + 1 / 2 by ring]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith)] at ht
  obtain ⟨h1, h2⟩ := ht
  have habs : |t - c| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]; constructor <;> linarith
  simp only [bump, ContinuousMap.coe_mk]
  rw [← QuotientAddGroup.mk_sub, (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 habs]


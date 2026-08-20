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

theorem fract_mem_of_norm_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hy : ‖((y : AddCircle (1 : ℝ)) - (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)))‖ < (b - a) / 2) :
    Int.fract y ∈ Set.Ico a b := by
  rw [← QuotientAddGroup.mk_sub, AddCircle.norm_eq] at hy
  set k : ℤ := round ((1 : ℝ)⁻¹ * (y - (a + b) / 2)) with hk
  have hlt : |y - (a + b) / 2 - k| < (b - a) / 2 := by
    have h : y - (a + b) / 2 - (k : ℝ) * 1 = y - (a + b) / 2 - k := by ring
    rwa [h] at hy
  rw [abs_lt] at hlt
  have h1 : a < y - k := by linarith [hlt.1]
  have h2 : y - k < b := by linarith [hlt.2]
  have hfr : Int.fract y = y - k := by
    rw [← Int.fract_sub_intCast y k, Int.fract_eq_self]
    constructor <;> linarith
  rw [hfr]
  exact ⟨h1.le, h2⟩

/-! ### Weyl's criterion -/


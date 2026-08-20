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

theorem norm_le_of_fract_mem {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hy : Int.fract y ∈ Set.Ico a b) :
    ‖((y : AddCircle (1 : ℝ)) - (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)))‖ ≤ (b - a) / 2 := by
  obtain ⟨hy1, hy2⟩ := hy
  have hfr : ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
    rw [Int.fract]; simp
  rw [← hfr, ← QuotientAddGroup.mk_sub]
  have habs : |Int.fract y - (a + b) / 2| ≤ (b - a) / 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |Int.fract y - (a + b) / 2| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one]
    linarith [Int.fract_nonneg y, Int.fract_lt_one y]
  rw [(AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 h2]
  exact habs


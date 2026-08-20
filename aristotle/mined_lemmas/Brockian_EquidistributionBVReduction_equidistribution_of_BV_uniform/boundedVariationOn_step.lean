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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem boundedVariationOn_step (a : ℝ) :
    BoundedVariationOn (fun t : ℝ => if a ≤ t then (1 : ℝ) else 0) (Set.Icc 0 1) := by
  have hmono : MonotoneOn (fun t : ℝ => if a ≤ t then (1 : ℝ) else 0) (Set.Icc (0:ℝ) 1) := by
    intro s _ t _ hst
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (h1.trans hst) h2
    · norm_num
    · exact le_rfl
  have h2 := hmono.eVariationOn_le (a := (0:ℝ)) (b := (1:ℝ)) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h2
  exact (h2.trans_lt ENNReal.ofReal_lt_top).ne

/-- The indicator of an interval has bounded variation on `[0,1]`. -/

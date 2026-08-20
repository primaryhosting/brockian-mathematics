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

theorem boundedVariationOn_indIco {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (indIco a b) (Set.Icc 0 1) := by
  have heq : indIco a b = fun t : ℝ =>
      (if a ≤ t then (1:ℝ) else 0) + (-(if b ≤ t then (1:ℝ) else 0)) := by
    funext t
    simp only [indIco, Set.mem_Ico]
    rcases le_or_gt a t with h1 | h1
    · rcases le_or_gt b t with h2 | h2
      · rw [if_neg (fun hc => absurd hc.2 (not_lt.2 h2)), if_pos h1, if_pos h2]; ring
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_neg (not_le.2 h2)]; ring
    · rw [if_neg (fun hc => absurd hc.1 (not_le.2 h1)), if_neg (not_le.2 h1),
        if_neg (not_le.2 (lt_of_lt_of_le h1 hab))]; ring
  rw [BoundedVariationOn, heq]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_add_le _ _ _)
  rw [eVariationOn_neg]
  exact ENNReal.add_ne_top.2 ⟨boundedVariationOn_step a, boundedVariationOn_step b⟩

/-- The integral of the indicator of `[a,b) ⊆ [0,1]` over `[0,1]` is `b - a`. -/

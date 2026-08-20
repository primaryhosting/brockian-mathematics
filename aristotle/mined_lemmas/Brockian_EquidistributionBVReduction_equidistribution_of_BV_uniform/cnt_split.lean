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

theorem cnt_split (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    cnt x N 0 b = cnt x N 0 a + cnt x N a b := by
  classical
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
    constructor
    · rintro ⟨hn, h0, hb⟩
      rcases lt_or_ge (Int.fract (x n)) a with hlt | hge
      · exact Or.inl ⟨hn, h0, hlt⟩
      · exact Or.inr ⟨hn, hge, hb⟩
    · rintro (⟨hn, h0, hb⟩ | ⟨hn, h0, hb⟩)
      · exact ⟨hn, h0, hb.trans_le hab⟩
      · exact ⟨hn, ha.trans h0, hb⟩
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_filter, Set.mem_Ico] at hn hn'
    exact absurd hn'.2.1 (not_le.2 hn.2.2)

/-- Monotonicity of the normalized counting function in the right endpoint. -/

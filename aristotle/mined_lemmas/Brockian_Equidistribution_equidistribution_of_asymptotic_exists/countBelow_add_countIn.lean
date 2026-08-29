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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` is smaller than `a`. -/

lemma countBelow_add_countIn (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    countBelow x N a + countIn x N a b = countBelow x N b := by
  classical
  have hsplit :
      (Finset.range N).filter (fun n => Int.fract (x n) < b) =
        ((Finset.range N).filter (fun n => Int.fract (x n) < a)) ∪
          ((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hlt⟩
      rcases lt_or_ge (Int.fract (x n)) a with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h, hlt⟩
    · rintro (⟨hn, h⟩ | ⟨hn, h1, h2⟩)
      · exact ⟨hn, lt_of_lt_of_le h hab⟩
      · exact ⟨hn, h2⟩
  have hdisj :
      Disjoint ((Finset.range N).filter (fun n => Int.fract (x n) < a))
        ((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) := by
    refine Finset.disjoint_left.2 ?_
    intro n hn hn'
    simp only [Finset.mem_filter] at hn hn'
    exact absurd hn'.2.1 (not_le.2 hn.2)
  rw [countBelow, countBelow, countIn, hsplit, Finset.card_union_of_disjoint hdisj]

/-- **Equidistribution on subintervals.**  Under the hypotheses of
`equidistribution_of_asymptotic_exists`, the proportion of the first `N` terms whose
fractional part lies in `[a, b) ⊆ [0, 1]` tends to the length `b - a`. -/

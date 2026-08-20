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

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Insert `a` into a list, placing it before the first element that is `≥ a`. -/

lemma pairwise_orderedInsert (a : α) (l : List α) (hl : l.Pairwise (· ≤ ·)) :
    (orderedInsert a l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b l ih =>
      rw [List.pairwise_cons] at hl
      by_cases h : a ≤ b
      · simp only [orderedInsert, h, if_true]
        rw [List.pairwise_cons]
        refine ⟨?_, by rw [List.pairwise_cons]; exact hl⟩
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h
        · exact le_trans h (hl.1 c hc)
      · simp only [orderedInsert, h, if_false]
        rw [List.pairwise_cons]
        refine ⟨?_, ih hl.2⟩
        intro c hc
        have hc' : c ∈ a :: l := (orderedInsert_perm a l).mem_iff.1 hc
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact le_of_not_ge h
        · exact hl.1 c hc'

/-- `insertionSort` returns a sorted permutation of its input. -/

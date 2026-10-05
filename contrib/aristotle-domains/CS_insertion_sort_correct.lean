/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Statement: insertionSort returns a sorted permutation of its input.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert a (insertionSort l)

lemma orderedInsert_perm (a : α) (l : List α) :
    (orderedInsert a l).Perm (a :: l) := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b l ih =>
      by_cases h : a ≤ b
      · simp [orderedInsert, h]
      · simp only [orderedInsert, h, if_false]
        exact ((ih.cons b).trans (List.Perm.swap a b l))

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
theorem insertion_sort_correct (l : List α) :
    (insertionSort l).Pairwise (· ≤ ·) ∧ (insertionSort l).Perm l := by
  induction l with
  | nil => exact ⟨by simp [insertionSort], by simp [insertionSort]⟩
  | cons a l ih =>
      refine ⟨pairwise_orderedInsert a _ ih.1, ?_⟩
      exact (orderedInsert_perm a (insertionSort l)).trans (ih.2.cons a)

end CS


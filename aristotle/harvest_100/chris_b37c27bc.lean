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

/-- Insert `a` into the (assumed sorted) list `l`, keeping it sorted. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert a ([] : List α) = [a] := rfl

theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert a (b :: l) =
      if a ≤ b then a :: b :: l else b :: orderedInsert a l := rfl

@[simp] theorem insertionSort_nil : insertionSort ([] : List α) = [] := rfl

@[simp] theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort (a :: l) = orderedInsert a (insertionSort l) := rfl

/-- Inserting an element produces a permutation of consing it on. -/
theorem orderedInsert_perm (a : α) (l : List α) : (orderedInsert a l).Perm (a :: l) := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [orderedInsert_cons]
      by_cases h : a ≤ b
      · simp [h]
      · simp only [h, if_false]
        exact ((ih.cons b).trans (List.Perm.swap a b l))

/-- Membership in `orderedInsert`. -/
@[simp] theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert a l ↔ b = a ∨ b ∈ l := by
  have := (orderedInsert_perm a l).mem_iff (a := b)
  simpa using this

/-- Inserting into a sorted list yields a sorted list. -/
theorem sorted_orderedInsert (a : α) {l : List α} (hl : l.Pairwise (· ≤ ·)) :
    (orderedInsert a l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [List.pairwise_cons] at hl
      obtain ⟨hb, hls⟩ := hl
      rw [orderedInsert_cons]
      by_cases h : a ≤ b
      · rw [if_pos h, List.pairwise_cons]
        refine ⟨?_, by rw [List.pairwise_cons]; exact ⟨hb, hls⟩⟩
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h
        · exact le_trans h (hb c hc)
      · rw [if_neg h, List.pairwise_cons]
        refine ⟨?_, ih hls⟩
        intro c hc
        rcases mem_orderedInsert.1 hc with rfl | hc
        · exact le_of_not_ge h
        · exact hb c hc

/-- `insertionSort` returns a sorted permutation of its input. -/
theorem insertion_sort_correct (l : List α) :
    (insertionSort l).Pairwise (· ≤ ·) ∧ (insertionSort l).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hs, hp⟩ := ih
      refine ⟨sorted_orderedInsert a hs, ?_⟩
      exact (orderedInsert_perm a (insertionSort l)).trans (hp.cons a)

end CS


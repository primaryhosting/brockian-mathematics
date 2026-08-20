/-
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Insertion Sort Correct

A self-contained development of insertion sort and its correctness proof.
-/

namespace CS

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, assumed sorted with respect to `r`. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort with respect to the relation `r`. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert r a [] = [a] := rfl

theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: orderedInsert r a l := rfl

@[simp] theorem insertionSort_nil : insertionSort r ([] : List α) = [] := rfl

@[simp] theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort r (a :: l) = orderedInsert r a (insertionSort r l) := rfl

/-- `orderedInsert` produces a permutation of `a :: l`. -/
theorem perm_orderedInsert (a : α) : ∀ l : List α, List.Perm (orderedInsert r a l) (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    by_cases h : r a b
    · simp [orderedInsert_cons, h]
    · simpa [orderedInsert_cons, h] using
        ((perm_orderedInsert a l).cons b).trans (List.Perm.swap a b l)

/-- Insertion sort returns a permutation of its input. -/
theorem perm_insertionSort : ∀ l : List α, List.Perm (insertionSort r l) l
  | [] => List.Perm.refl _
  | a :: l => by
    simpa using (perm_orderedInsert r a (insertionSort r l)).trans
      ((perm_insertionSort l).cons a)

section Total

variable [Std.Total r] [IsTrans α r]

theorem sorted_orderedInsert (a : α) :
    ∀ l : List α, List.Pairwise r l → List.Pairwise r (orderedInsert r a l)
  | [], _ => by simp
  | b :: l, hl => by
    rw [orderedInsert_cons]
    rcases List.pairwise_cons.1 hl with ⟨hb, hl'⟩
    by_cases h : r a b
    · rw [if_pos h]
      refine List.pairwise_cons.2 ⟨?_, hl⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact _root_.trans h (hb c hc)
    · rw [if_neg h]
      refine List.pairwise_cons.2 ⟨?_, sorted_orderedInsert a l hl'⟩
      intro c hc
      have hmem : c ∈ a :: l :=
        (perm_orderedInsert r a l).mem_iff.1 hc
      rcases List.mem_cons.1 hmem with rfl | hc'
      · exact (Std.Total.total (r := r) _ b).resolve_left h
      · exact hb c hc'

/-- Insertion sort produces a sorted (pairwise-`r`) list. -/
theorem sorted_insertionSort : ∀ l : List α, List.Pairwise r (insertionSort r l)
  | [] => by simp
  | a :: l => by
    simpa using sorted_orderedInsert r a (insertionSort r l) (sorted_insertionSort l)

/-- **Insertion sort is correct**: for a total, transitive, decidable relation `r`,
`insertionSort r l` is a list that is sorted with respect to `r` and is a
permutation of the input list `l`. -/
theorem insertion_sort_correct (l : List α) :
    List.Pairwise r (insertionSort r l) ∧ List.Perm (insertionSort r l) l :=
  ⟨sorted_insertionSort r l, perm_insertionSort r l⟩

end Total

/-- Sanity check on a concrete list of naturals. -/
example : insertionSort (· ≤ ·) [3, 1, 2, 1] = [1, 1, 2, 3] := by decide

end CS

#print axioms CS.insertion_sort_correct

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


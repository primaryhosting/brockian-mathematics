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
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, assumed sorted with respect to `r`, at the first
position where `a` compares below the current head. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort: repeatedly insert the head into the sorted tail. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert r a [] = [a] := rfl

theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: orderedInsert r a l := rfl

@[simp] theorem insertionSort_nil : insertionSort r [] = [] := rfl

theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort r (a :: l) = orderedInsert r a (insertionSort r l) := rfl

/-- Inserting an element produces a permutation of consing it on. -/
theorem orderedInsert_perm (a : α) : ∀ l : List α, (orderedInsert r a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      rw [orderedInsert_cons]
      split
      · exact List.Perm.refl _
      · exact ((orderedInsert_perm a l).cons b).trans (List.Perm.swap a b l)

/-- Membership in `orderedInsert` is membership in the original list, plus the inserted element. -/
theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert r a l ↔ b = a ∨ b ∈ l := by
  have := (orderedInsert_perm r a l).mem_iff (a := b)
  simpa using this

/-- Insertion sort returns a permutation of its input. -/
theorem insertionSort_perm : ∀ l : List α, (insertionSort r l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
      rw [insertionSort_cons]
      exact (orderedInsert_perm r a _).trans ((insertionSort_perm l).cons a)

variable (htotal : ∀ a b : α, r a b ∨ r b a)
  (htrans : ∀ a b c : α, r a b → r b c → r a c)

include htotal htrans in
/-- Inserting into a sorted list yields a sorted list. -/
theorem pairwise_orderedInsert (a : α) :
    ∀ l : List α, l.Pairwise r → (orderedInsert r a l).Pairwise r
  | [], _ => List.pairwise_singleton r a
  | b :: l, h => by
      rw [List.pairwise_cons] at h
      rw [orderedInsert_cons]
      split
      · rename_i hab
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hab
        · exact htrans _ _ _ hab (h.1 c hc)
      · rename_i hab
        have hba : r b a := (htotal a b).resolve_left hab
        refine List.pairwise_cons.2
          ⟨?_, pairwise_orderedInsert a l h.2⟩
        intro c hc
        rcases (mem_orderedInsert r).1 hc with rfl | hc
        · exact hba
        · exact h.1 c hc

include htotal htrans in
/-- **Insertion sort is correct**: for a total, transitive (decidable) relation `r`,
`insertionSort r l` is sorted with respect to `r` (its elements are pairwise related
in order) and is a permutation of `l`. -/
theorem insertion_sort_correct (l : List α) :
    (insertionSort r l).Pairwise r ∧ (insertionSort r l).Perm l := by
  refine ⟨?_, insertionSort_perm r l⟩
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih => exact pairwise_orderedInsert r htotal htrans a _ ih

/-- Concrete instance: sorting a list of naturals by `≤`. -/
example (l : List ℕ) :
    (insertionSort (· ≤ ·) l).Pairwise (· ≤ ·) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct _ (fun a b => Nat.le_total a b)
    (fun _ _ _ hab hbc => le_trans hab hbc) l

example : insertionSort (· ≤ ·) [3, 1, 2, 1] = [1, 1, 2, 3] := by decide

end CS

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


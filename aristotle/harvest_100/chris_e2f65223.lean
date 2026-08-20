/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, in front of the first element `b` of `l` with `r a b`. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort with respect to the relation `r`. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert r a [] = [a] := rfl

@[simp] theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: orderedInsert r a l := rfl

@[simp] theorem insertionSort_nil : insertionSort r ([] : List α) = [] := rfl

@[simp] theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort r (a :: l) = orderedInsert r a (insertionSort r l) := rfl

/-- `orderedInsert r a l` is a permutation of `a :: l`. -/
theorem perm_orderedInsert (a : α) :
    ∀ l : List α, (orderedInsert r a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      by_cases h : r a b
      · rw [orderedInsert_cons, if_pos h]
      · rw [orderedInsert_cons, if_neg h]
        exact ((perm_orderedInsert a l).cons b).trans (List.Perm.swap a b l)

/-- The output of `insertionSort` is a permutation of its input. -/
theorem perm_insertionSort : ∀ l : List α, (insertionSort r l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
      rw [insertionSort_cons]
      exact (perm_orderedInsert r a (insertionSort r l)).trans
        ((perm_insertionSort l).cons a)

theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert r a l ↔ b = a ∨ b ∈ l :=
  (perm_orderedInsert r a l).mem_iff.trans List.mem_cons

theorem mem_insertionSort {a : α} {l : List α} : a ∈ insertionSort r l ↔ a ∈ l :=
  (perm_insertionSort r l).mem_iff

section Total

variable (htotal : ∀ a b, r a b ∨ r b a) (htrans : ∀ {a b c}, r a b → r b c → r a c)

include htotal htrans in
/-- Inserting an element into a sorted list keeps it sorted. -/
theorem sorted_orderedInsert (a : α) :
    ∀ l : List α, List.Pairwise r l → List.Pairwise r (orderedInsert r a l)
  | [], _ => List.pairwise_singleton r a
  | b :: l, hl => by
      have hbl : ∀ x ∈ l, r b x := (List.pairwise_cons.1 hl).1
      have hsl : List.Pairwise r l := (List.pairwise_cons.1 hl).2
      by_cases h : r a b
      · rw [orderedInsert_cons, if_pos h]
        refine List.pairwise_cons.2 ⟨?_, hl⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h
        · exact htrans h (hbl x hx)
      · have hba : r b a := (htotal a b).resolve_left h
        rw [orderedInsert_cons, if_neg h]
        refine List.pairwise_cons.2 ⟨?_, sorted_orderedInsert a l hsl⟩
        intro x hx
        rcases (mem_orderedInsert r).1 hx with rfl | hx
        · exact hba
        · exact hbl x hx

include htotal htrans in
/-- The output of `insertionSort` is sorted, i.e. pairwise related by `r`. -/
theorem sorted_insertionSort : ∀ l : List α, List.Pairwise r (insertionSort r l)
  | [] => List.Pairwise.nil
  | a :: l => by
      rw [insertionSort_cons]
      exact sorted_orderedInsert r htotal (fun h₁ h₂ => htrans h₁ h₂) a _
        (sorted_insertionSort l)

include htotal htrans in
/-- **Insertion sort is correct**: for a total, transitive relation `r`, the list
`insertionSort r l` is sorted (pairwise related by `r`) and is a permutation of `l`. -/
theorem insertion_sort_correct (l : List α) :
    List.Pairwise r (insertionSort r l) ∧ (insertionSort r l).Perm l :=
  ⟨sorted_insertionSort r htotal (fun h₁ h₂ => htrans h₁ h₂) l, perm_insertionSort r l⟩

end Total

/-- Sanity check: the hypotheses are satisfiable, e.g. by `≤` on `Nat`. -/
example (l : List Nat) :
    List.Pairwise (· ≤ ·) (insertionSort (· ≤ ·) l) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct _ Nat.le_total (fun h₁ h₂ => Nat.le_trans h₁ h₂) l

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


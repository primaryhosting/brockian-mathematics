/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (Lean's `Init` prelude only), because a
module doc comment such as the header above must be the very first command in a
file and therefore cannot be preceded by `import` lines.  Everything used below
(`List.Perm`, `List.Pairwise`, `DecidableRel`) is part of the Lean 4 core
library, and `List.Pairwise r` is by definition Mathlib's `List.Sorted r`.
The Mathlib-facing corollaries (`List.Sorted (· ≤ ·)` for a `LinearOrder`, and
agreement with `List.insertionSort`) live in `RequestProject.Main`.
-/

namespace CS

universe u

variable {α : Type u}

section

variable (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, in front of the first element `b` with `r a b`. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l

/-- Insertion sort with respect to the relation `r`. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert r a [] = [a] := rfl

@[simp] theorem insertionSort_nil : insertionSort r ([] : List α) = [] := rfl

@[simp] theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort r (a :: l) = orderedInsert r a (insertionSort r l) := rfl

variable {r}

/-- `orderedInsert` produces a permutation of the list with `a` prepended. -/
theorem perm_orderedInsert (a : α) : ∀ l : List α, (orderedInsert r a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      by_cases h : r a b
      · simp [orderedInsert, h]
      · simpa [orderedInsert, h] using
          ((perm_orderedInsert a l).cons b).trans (List.Perm.swap a b l)

/-- Inserting into a sorted list keeps it sorted, provided `r` is transitive and total. -/
theorem pairwise_orderedInsert (htrans : ∀ x y z, r x y → r y z → r x z)
    (htotal : ∀ x y, r x y ∨ r y x) (a : α) :
    ∀ {l : List α}, l.Pairwise r → (orderedInsert r a l).Pairwise r
  | [], _ => by simp
  | b :: l, hp => by
      rw [List.pairwise_cons] at hp
      by_cases h : r a b
      · simp only [orderedInsert, if_pos h, List.pairwise_cons]
        refine ⟨?_, hp.1, hp.2⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h
        · exact htrans _ _ _ h (hp.1 x hx)
      · have hba : r b a := (htotal a b).resolve_left h
        simp only [orderedInsert, if_neg h, List.pairwise_cons]
        refine ⟨?_, pairwise_orderedInsert htrans htotal a hp.2⟩
        intro x hx
        rcases List.mem_cons.1 ((perm_orderedInsert a l).mem_iff.1 hx) with rfl | hx
        · exact hba
        · exact hp.1 x hx

/-- **Insertion sort is correct**: for a transitive and total (decidable) relation `r`,
`insertionSort r l` is sorted with respect to `r` (i.e. pairwise related, which is
the definition of `List.Sorted r`) and is a permutation of `l`. -/
theorem insertion_sort_correct (htrans : ∀ x y z, r x y → r y z → r x z)
    (htotal : ∀ x y, r x y ∨ r y x) (l : List α) :
    (insertionSort r l).Pairwise r ∧ (insertionSort r l).Perm l := by
  induction l with
  | nil => exact ⟨List.Pairwise.nil, List.Perm.refl _⟩
  | cons a l ih =>
      exact ⟨pairwise_orderedInsert htrans htotal a ih.1,
        (perm_orderedInsert a _).trans (ih.2.cons a)⟩

end

end CS

import Mathlib
import RequestProject.InsertionSort

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



/-!
Mathlib-facing corollaries of `CS.insertion_sort_correct`.
-/

namespace CS

variable {α : Type*}

/-- The `CS` insertion sort agrees with Mathlib's `List.insertionSort`. -/
theorem insertionSort_eq (r : α → α → Prop) [DecidableRel r] (l : List α) :
    CS.insertionSort r l = List.insertionSort r l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have haux : ∀ m : List α, CS.orderedInsert r a m = List.orderedInsert r a m := by
        intro m
        induction m with
        | nil => rfl
        | cons b m ihm => by_cases h : r a b <;> simp [CS.orderedInsert, List.orderedInsert, h, ihm]
      simp [CS.insertionSort, List.insertionSort, ih, haux]

/-- Insertion sort on a linear order returns a sorted permutation of its input. -/
theorem insertionSort_sorted_perm [LinearOrder α] (l : List α) :
    List.Pairwise (fun x y : α => x ≤ y) (CS.insertionSort (fun x y : α => x ≤ y) l) ∧
      (CS.insertionSort (fun x y : α => x ≤ y) l).Perm l :=
  CS.insertion_sort_correct (r := fun x y : α => x ≤ y)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂) (fun x y => le_total x y) l

end CS

#print axioms CS.insertion_sort_correct
#print axioms CS.insertionSort_eq
#print axioms CS.insertionSort_sorted_perm


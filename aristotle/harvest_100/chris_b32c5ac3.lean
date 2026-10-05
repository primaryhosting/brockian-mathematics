/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required file header above is a *module docstring*, which Lean treats as a
command, so no `import` line may follow it.  The development below is therefore self-contained,
using only the `List.Perm` / `List.Pairwise` API available without imports.

Mathlib proves the same statement for its own `List.insertionSort` via
`List.pairwise_insertionSort` (sortedness) and `List.perm_insertionSort` (permutation);
the file `RequestProject/CSMathlib.lean` records that these agree with the definitions here.
-/

namespace CS

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, before the first element `b` with `r a b`. -/
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

/-- `orderedInsert` produces a permutation of the list with the new element consed on. -/
theorem perm_orderedInsert (a : α) : ∀ l : List α, (orderedInsert r a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      rw [orderedInsert_cons]
      split
      · exact List.Perm.refl _
      · exact ((perm_orderedInsert a l).cons b).trans (List.Perm.swap a b l)

theorem mem_orderedInsert {a x : α} {l : List α} :
    x ∈ orderedInsert r a l ↔ x = a ∨ x ∈ l := by
  have h := (perm_orderedInsert r a l).mem_iff (a := x)
  simpa using h

/-- `insertionSort` returns a permutation of its input. -/
theorem perm_insertionSort : ∀ l : List α, (insertionSort r l).Perm l
  | [] => List.Perm.refl _
  | a :: l =>
      (perm_orderedInsert r a (insertionSort r l)).trans ((perm_insertionSort l).cons a)

variable (total : ∀ a b : α, r a b ∨ r b a)
variable (trans : ∀ a b c : α, r a b → r b c → r a c)

include total trans in
/-- Inserting into a sorted list keeps it sorted. -/
theorem pairwise_orderedInsert (a : α) :
    ∀ {l : List α}, l.Pairwise r → (orderedInsert r a l).Pairwise r
  | [], _ => by simp
  | b :: l, h => by
      rw [List.pairwise_cons] at h
      rw [orderedInsert_cons]
      split
      · rename_i hab
        refine List.Pairwise.cons ?_ (List.pairwise_cons.2 h)
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hab
        · exact trans _ _ _ hab (h.1 x hx)
      · rename_i hab
        have hba : r b a := (total a b).resolve_left hab
        refine List.Pairwise.cons ?_ (pairwise_orderedInsert a h.2)
        intro x hx
        rcases (mem_orderedInsert r).1 hx with rfl | hx
        · exact hba
        · exact h.1 x hx

include total trans in
/-- `insertionSort` returns a sorted list. -/
theorem pairwise_insertionSort : ∀ l : List α, (insertionSort r l).Pairwise r
  | [] => List.Pairwise.nil
  | a :: l => pairwise_orderedInsert r total trans a (pairwise_insertionSort l)

include total trans in
/-- **Insertion sort is correct**: for a decidable, total, transitive relation `r`,
`insertionSort r l` is sorted with respect to `r` and is a permutation of the input `l`. -/
theorem insertion_sort_correct (l : List α) :
    (insertionSort r l).Pairwise r ∧ (insertionSort r l).Perm l :=
  ⟨pairwise_insertionSort r total trans l, perm_insertionSort r l⟩

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

import Mathlib
import RequestProject.CS

/-!
# Insertion sort: agreement with Mathlib

The self-contained development in `RequestProject/CS.lean` defines `CS.insertionSort`, which
agrees definitionally with Mathlib's `List.insertionSort`.  Consequently `CS.insertion_sort_correct`
matches Mathlib's `List.pairwise_insertionSort` and `List.perm_insertionSort`.
-/

namespace CS

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

theorem orderedInsert_eq (a : α) : ∀ l : List α,
    orderedInsert r a l = List.orderedInsert r a l
  | [] => rfl
  | b :: l => by
      rw [orderedInsert_cons, List.orderedInsert, orderedInsert_eq a l]

theorem insertionSort_eq : ∀ l : List α, insertionSort r l = List.insertionSort r l
  | [] => rfl
  | a :: l => by
      rw [insertionSort, insertionSort_eq l, orderedInsert_eq]
      simp [List.insertionSort]

/-- Correctness of insertion sort, stated for Mathlib's `List.insertionSort`,
using `List.pairwise_insertionSort` and `List.perm_insertionSort`. -/
theorem insertion_sort_correct' [Std.Total r] [IsTrans α r] (l : List α) :
    (List.insertionSort r l).Pairwise r ∧ (List.insertionSort r l).Perm l :=
  ⟨List.pairwise_insertionSort r l, List.perm_insertionSort r l⟩

end CS


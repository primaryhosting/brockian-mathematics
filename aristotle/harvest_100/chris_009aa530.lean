import Mathlib

/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- **Insertion sort is correct**: for a decidable, total, transitive relation `r`,
`List.insertionSort r l` is sorted with respect to `r` and is a permutation of `l`.

Both halves come directly from Mathlib (`Mathlib/Data/List/Sort.lean`):
`List.pairwise_insertionSort` and `List.perm_insertionSort`. -/
theorem insertion_sort_correct {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [Trans r r r] (l : List α) :
    List.Pairwise r (List.insertionSort r l) ∧ (List.insertionSort r l).Perm l :=
  ⟨List.pairwise_insertionSort r l, List.perm_insertionSort r l⟩

/-- Concrete instance for `ℕ` with `≤`. -/
theorem insertion_sort_correct_nat (l : List ℕ) :
    List.Pairwise (· ≤ ·) (List.insertionSort (· ≤ ·) l) ∧
      (List.insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) l

end CS

#print axioms CS.insertion_sort_correct


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

theorem sorted_insertionSort : ∀ l : List α, List.Pairwise r (insertionSort r l)
  | [] => by simp
  | a :: l => by
    simpa using sorted_orderedInsert r a (insertionSort r l) (sorted_insertionSort l)

/-- **Insertion sort is correct**: for a total, transitive, decidable relation `r`,
`insertionSort r l` is a list that is sorted with respect to `r` and is a
permutation of the input list `l`. -/

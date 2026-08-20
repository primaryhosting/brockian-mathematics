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

theorem perm_orderedInsert (a : α) : ∀ l : List α, List.Perm (orderedInsert r a l) (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    by_cases h : r a b
    · simp [orderedInsert_cons, h]
    · simpa [orderedInsert_cons, h] using
        ((perm_orderedInsert a l).cons b).trans (List.Perm.swap a b l)

/-- Insertion sort returns a permutation of its input. -/

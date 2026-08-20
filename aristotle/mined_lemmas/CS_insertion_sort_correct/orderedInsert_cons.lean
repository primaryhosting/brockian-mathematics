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

theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: orderedInsert r a l := rfl


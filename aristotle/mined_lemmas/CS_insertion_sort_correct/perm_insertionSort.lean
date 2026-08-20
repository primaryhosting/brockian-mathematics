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

theorem perm_insertionSort : ∀ l : List α, List.Perm (insertionSort r l) l
  | [] => List.Perm.refl _
  | a :: l => by
    simpa using (perm_orderedInsert r a (insertionSort r l)).trans
      ((perm_insertionSort l).cons a)

section Total

variable [Std.Total r] [IsTrans α r]


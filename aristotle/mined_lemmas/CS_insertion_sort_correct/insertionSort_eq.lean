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

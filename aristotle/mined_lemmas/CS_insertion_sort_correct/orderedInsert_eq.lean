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

theorem orderedInsert_eq (a : α) : ∀ l : List α,
    orderedInsert r a l = List.orderedInsert r a l
  | [] => rfl
  | b :: l => by
      rw [orderedInsert_cons, List.orderedInsert, orderedInsert_eq a l]


import Mathlib
import RequestProject.Main

/-!
# Insertion sort correctness, stated with Mathlib's `List.Sorted`

`RequestProject/Main.lean` contains the target theorem `CS.insertion_sort_correct`
(it cannot contain an `import` line, since the mandated header comment must be the
first command of the file).  Here we restate it in Mathlib vocabulary, for a
`LinearOrder`, using `List.Pairwise (· ≤ ·)` (which is Mathlib's `List.Sorted (· ≤ ·)`).
-/

set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- **Insertion sort is correct** (Mathlib phrasing): over a linear order,
`CS.insertionSort (· ≤ ·) l` is sorted (pairwise `≤`) and is a permutation of `l`. -/

theorem insertionSort_eq_list_insertionSort (l : List α) :
    insertionSort (· ≤ ·) l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [insertionSort_cons, ih, List.insertionSort_cons]
    generalize l.insertionSort (· ≤ ·) = m
    induction m with
    | nil => rfl
    | cons b m ihm =>
      by_cases h : a ≤ b <;> simp [orderedInsert_cons, h, ihm]

end CS

/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to come before any other
command, and a module docstring `/-! ... -/` counts as a command.  Since the header
comment above must be the very first thing in this file, no `import` line can follow it.
The development below is therefore written against the Lean 4 core library only
(`List.Perm`, `List.Pairwise`, which are the same notions Mathlib uses:
`List.Sorted r = List.Pairwise r`).
-/

set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} (le : α → α → Prop) [DecidableRel le]

/-- `orderedInsert le a l` inserts `a` into the list `l` just before the first element
`b` with `le a b`. -/

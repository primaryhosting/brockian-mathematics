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

theorem perm_orderedInsert (a : α) : ∀ l : List α, (orderedInsert le a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    by_cases h : le a b
    · simp [h]
    · have : ((b :: orderedInsert le a l) : List α).Perm (b :: a :: l) :=
        (perm_orderedInsert a l).cons b
      simpa [h] using this.trans (List.Perm.swap a b l)

/-- Inserting into a sorted list keeps it sorted. -/

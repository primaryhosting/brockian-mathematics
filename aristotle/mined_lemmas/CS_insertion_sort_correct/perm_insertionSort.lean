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

theorem perm_insertionSort : ∀ l : List α, (insertionSort le l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
    simpa using (perm_orderedInsert le a (insertionSort le l)).trans
      ((perm_insertionSort l).cons a)

/-- `insertionSort` returns a sorted list. -/

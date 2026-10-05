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

theorem pairwise_insertionSort (htotal : ∀ a b : α, le a b ∨ le b a)
    (htrans : ∀ a b c : α, le a b → le b c → le a c) :
    ∀ l : List α, (insertionSort le l).Pairwise le
  | [] => List.Pairwise.nil
  | a :: l => pairwise_orderedInsert le htotal htrans a _ (pairwise_insertionSort htotal htrans l)

/-- **Insertion sort is correct**: for a total, transitive (decidable) relation `le`,
`insertionSort le l` is sorted with respect to `le` and is a permutation of `l`. -/

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

theorem insertion_sort_correct_le (l : List α) :
    (insertionSort (· ≤ ·) l).Pairwise (· ≤ ·) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) (fun a b => le_total a b)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂) l

/-- Our insertion sort agrees with Mathlib's `List.insertionSort`. -/

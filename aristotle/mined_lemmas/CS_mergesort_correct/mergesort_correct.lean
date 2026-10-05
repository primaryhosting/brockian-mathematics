import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem mergesort_correct (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c)
    (l : List α) :
    List.Pairwise r (mergeSort r l) ∧ (mergeSort r l).Perm l :=
  ⟨mergeSort_pairwise r htotal htrans l, mergeSort_perm r l⟩

end CS


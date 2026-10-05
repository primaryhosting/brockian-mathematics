import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem mergeSort_pairwise (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c) :
    ∀ l : List α, List.Pairwise r (mergeSort r l)
  | [] => by rw [mergeSort]; exact List.Pairwise.nil
  | [x] => by rw [mergeSort]; simp
  | x :: y :: t => by
      rw [mergeSort]
      exact merge_pairwise r htotal htrans _ _
        (mergeSort_pairwise r htotal htrans (split (x :: y :: t)).1)
        (mergeSort_pairwise r htotal htrans (split (x :: y :: t)).2)
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t

/-- **Mergesort is correct**: for a total, transitive (decidable) relation `r`,
`mergeSort r l` is sorted with respect to `r` (i.e. pairwise `r`-related, in order)
and is a permutation of the input list `l`. -/

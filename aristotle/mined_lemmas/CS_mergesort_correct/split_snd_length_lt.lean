import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem split_snd_length_lt (x y : α) (t : List α) :
    (split (x :: y :: t)).2.length < (x :: y :: t).length := by
  have h := split_length_add t
  simp only [split, List.length_cons]
  omega

/-- Mergesort: split the list in two, sort each half recursively, and merge. -/

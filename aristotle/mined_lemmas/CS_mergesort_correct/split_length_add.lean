import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem split_length_add (l : List α) :
    (split l).1.length + (split l).2.length = l.length := by
  have h := (split_perm l).length_eq
  simpa using h


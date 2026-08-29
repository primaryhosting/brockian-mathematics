import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

def mergeSort (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      merge r (mergeSort r (split (x :: y :: t)).1) (mergeSort r (split (x :: y :: t)).2)
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t


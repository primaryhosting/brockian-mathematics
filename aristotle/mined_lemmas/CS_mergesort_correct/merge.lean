import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

def merge (r : α → α → Prop) [DecidableRel r] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if r x y then x :: merge r xs (y :: ys) else y :: merge r (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Split a list into two lists by alternating elements. -/

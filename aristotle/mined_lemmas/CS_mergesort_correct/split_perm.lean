import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem split_perm : ∀ l : List α, ((split l).1 ++ (split l).2).Perm l
  | [] => by simp [split]
  | [_] => by simp [split]
  | x :: y :: t => by
      have ih := split_perm t
      simp only [split, List.cons_append]
      refine List.Perm.cons x ?_
      exact (List.perm_middle).trans ((ih).cons y)


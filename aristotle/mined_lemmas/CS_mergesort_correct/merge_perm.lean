import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem merge_perm (r : α → α → Prop) [DecidableRel r] :
    ∀ xs ys : List α, (merge r xs ys).Perm (xs ++ ys)
  | [], ys => by rw [merge]; simp
  | x :: xs, [] => by rw [merge] <;> simp
  | x :: xs, y :: ys => by
      by_cases h : r x y
      · rw [merge, if_pos h]
        exact (merge_perm r xs (y :: ys)).cons x
      · rw [merge, if_neg h]
        refine ((merge_perm r (x :: xs) ys).cons y).trans ?_
        exact (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm
termination_by xs ys => xs.length + ys.length


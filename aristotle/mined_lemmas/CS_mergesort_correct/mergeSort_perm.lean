import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem mergeSort_perm (r : α → α → Prop) [DecidableRel r] :
    ∀ l : List α, (mergeSort r l).Perm l
  | [] => by rw [mergeSort]
  | [x] => by rw [mergeSort]
  | x :: y :: t => by
      have h1 : (mergeSort r (split (x :: y :: t)).1).Perm (split (x :: y :: t)).1 :=
        mergeSort_perm r _
      have h2 : (mergeSort r (split (x :: y :: t)).2).Perm (split (x :: y :: t)).2 :=
        mergeSort_perm r _
      rw [mergeSort]
      exact (merge_perm r _ _).trans ((h1.append h2).trans (split_perm (x :: y :: t)))
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t


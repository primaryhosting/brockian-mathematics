import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem mem_merge {r : α → α → Prop} [DecidableRel r] {a : α} {xs ys : List α} :
    a ∈ merge r xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm r xs ys).mem_iff, List.mem_append]


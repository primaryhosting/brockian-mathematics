import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, assumed sorted, into one list. -/

theorem sorted_mergeSort : ∀ l : List α, (mergeSort l).Pairwise (· ≤ ·)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: t => by
      rw [mergeSort]
      exact sorted_merge _ _ (sorted_mergeSort _) (sorted_mergeSort _)
  termination_by l => l.length
  decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- `mergeSort` returns a sorted permutation of its input. -/

/-
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, taking the smaller head at each step. -/

theorem pairwise_mergeSort (l : List α) : List.Pairwise (· ≤ ·) (mergeSort l) := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 a => simp [mergeSort]
  | case3 a b l ih₁ ih₂ =>
      rw [mergeSort]
      exact pairwise_merge ih₁ ih₂

/-- **Mergesort is correct**: `mergeSort` returns a sorted permutation of its input. -/

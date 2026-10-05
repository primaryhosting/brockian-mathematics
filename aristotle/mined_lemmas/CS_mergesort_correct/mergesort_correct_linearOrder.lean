import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem mergesort_correct_linearOrder {α : Type*} [LinearOrder α] (l : List α) :
    List.Pairwise (· ≤ ·) (CS.mergeSort (· ≤ · : α → α → Prop) l) ∧
      (CS.mergeSort (· ≤ · : α → α → Prop) l).Perm l :=
  CS.mergesort_correct _ le_total (fun _ _ _ hab hbc => le_trans hab hbc) l

end CS

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, and a module doc comment `/-! ... -/` may not precede them.
Since the header comment above must literally begin the file, this module is
written to be self-contained (it needs no imports beyond the prelude).
A Mathlib-facing corollary for linear orders lives in
`RequestProject/LinearOrderCorollary.lean`.
-/

set_option autoImplicit false

namespace CS

universe u

variable {α : Type u}

/-- Merge two lists with respect to a decidable relation `r`. -/

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Mergesort is correct.**

For any comparison `le : α → α → Bool` that is transitive and total, `List.mergeSort le l`
is sorted with respect to `le` (i.e. `List.Pairwise` holds for `le`) and is a permutation
of the input list `l`.

Both halves are provided by the standard library: `List.pairwise_mergeSort` gives
sortedness and `List.mergeSort_perm` gives the permutation property. -/
theorem mergesort_correct {α : Type u} (le : α → α → Bool)
    (trans : ∀ a b c : α, le a b → le b c → le a c)
    (total : ∀ a b : α, le a b || le b a) (l : List α) :
    (l.mergeSort le).Pairwise (fun a b => le a b) ∧ (l.mergeSort le).Perm l :=
  ⟨List.pairwise_mergeSort trans total l, List.mergeSort_perm l le⟩

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import RequestProject.MergesortCorrect

/-!
# Mergesort correctness, specialized to a `LinearOrder`

A Mathlib-flavoured corollary of `CS.mergesort_correct`.
-/

namespace CS

/-- **Mergesort is correct, for a linear order.** Sorting a list with `List.mergeSort`
using `(· ≤ ·)` yields a list that is `List.Pairwise (· ≤ ·)` and is a permutation of the
input. -/
theorem mergesort_correct_linearOrder {α : Type*} [LinearOrder α] (l : List α) :
    (l.mergeSort (fun a b => a ≤ b)).Pairwise (· ≤ ·) ∧
      (l.mergeSort (fun a b => a ≤ b)).Perm l := by
  obtain ⟨hsorted, hperm⟩ :=
    mergesort_correct (fun a b : α => decide (a ≤ b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total a b) l
  exact ⟨by simpa using hsorted, hperm⟩

end CS


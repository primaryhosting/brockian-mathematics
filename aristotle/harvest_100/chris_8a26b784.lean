import Mathlib
import RequestProject.MergesortCorrect

/-!
# Mergesort correctness in an arbitrary linear order

A Mathlib-flavoured corollary of `CS.mergesort_correct`: over any `LinearOrder`,
`List.mergeSort` with the boolean comparison `(· ≤ ·)` returns a sorted (pairwise `≤`)
permutation of its input.
-/

namespace CS

/-- Mergesort over a linear order returns a sorted permutation of its input. -/
theorem mergesort_correct_linearOrder {α : Type*} [LinearOrder α] (l : List α) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) ∧
      (l.mergeSort (fun a b => decide (a ≤ b))).Perm l := by
  obtain ⟨hs, hp⟩ := mergesort_correct (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp_all; exact le_trans hab hbc)
    (by intro a b; simp; exact le_total a b) l
  exact ⟨by simpa using hs, hp⟩

end CS

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Mergesort is correct.**

For any boolean comparison `le` on `α` that is transitive and total, `List.mergeSort le l`
is `le`-sorted (pairwise-related along the list) and is a permutation of `l`.

The two components are exactly the standard-library lemmas `List.pairwise_mergeSort`
(sortedness) and `List.mergeSort_perm` (permutation). -/
theorem mergesort_correct {α : Type u} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (l : List α) :
    (l.mergeSort le).Pairwise (fun a b => le a b = true) ∧ (l.mergeSort le).Perm l :=
  ⟨List.pairwise_mergeSort trans total l, List.mergeSort_perm l le⟩

/-- Mergesort on natural numbers with `≤`: the result is sorted and a permutation
of the input. -/
theorem mergesort_correct_nat (l : List Nat) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) ∧
      (l.mergeSort (fun a b => decide (a ≤ b))).Perm l := by
  obtain ⟨hs, hp⟩ := mergesort_correct (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp_all; omega) (by intro a b; simp; omega) l
  exact ⟨by simpa using hs, hp⟩

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


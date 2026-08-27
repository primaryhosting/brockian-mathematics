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
import RequestProject.Mergesort

/-!
# Mergesort Correct — specializations

Specializations of `CS.mergesort_correct` to a decidable total transitive relation,
and in particular to `(· ≤ ·)` on `ℕ`.
-/

universe u

namespace CS

/-- Mergesort correctness for a decidable total transitive relation `r`. -/
theorem mergesort_correct_rel {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (l : List α) :
    List.Pairwise r (l.mergeSort fun a b => decide (r a b)) ∧
      (l.mergeSort fun a b => decide (r a b)).Perm l :=
  ⟨List.pairwise_mergeSort' r l, List.mergeSort_perm l _⟩

/-- Mergesort correctness on `ℕ` with the usual order. -/
theorem mergesort_correct_nat (l : List ℕ) :
    List.Pairwise (· ≤ ·) (l.mergeSort fun a b => decide (a ≤ b)) ∧
      (l.mergeSort fun a b => decide (a ≤ b)).Perm l :=
  mergesort_correct_rel (· ≤ ·) l

end CS

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Mergesort is correct**: for a transitive and total boolean comparison `le`,
`List.mergeSort l le` is sorted with respect to `le` (i.e. `List.Pairwise`, which is
by definition Mathlib's `List.Sorted`) and is a permutation of `l`.

The two halves are exactly the library lemmas `List.pairwise_mergeSort`
and `List.mergeSort_perm`. -/
theorem mergesort_correct {α : Type u} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (l : List α) :
    List.Pairwise (fun a b => le a b = true) (l.mergeSort le) ∧ (l.mergeSort le).Perm l :=
  ⟨List.pairwise_mergeSort trans total l, List.mergeSort_perm l le⟩

end CS


/-
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Insertion Sort Correct

A self-contained development of insertion sort and its correctness proof.
-/

namespace CS

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, assumed sorted with respect to `r`. -/

theorem insertion_sort_correct (l : List α) :
    List.Pairwise r (insertionSort r l) ∧ List.Perm (insertionSort r l) l :=
  ⟨sorted_insertionSort r l, perm_insertionSort r l⟩

end Total

/-- Sanity check on a concrete list of naturals. -/
example : insertionSort (· ≤ ·) [3, 1, 2, 1] = [1, 1, 2, 3] := by decide

end CS

#print axioms CS.insertion_sort_correct

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


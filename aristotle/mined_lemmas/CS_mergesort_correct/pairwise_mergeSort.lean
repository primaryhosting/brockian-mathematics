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

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Merge two lists with respect to a decidable relation `r`.
The smaller head (according to `r`) is emitted first. -/

theorem pairwise_mergeSort (htot : ∀ a b : α, r a b ∨ r b a)
    (htrans : ∀ a b c : α, r a b → r b c → r a c) (l : List α) :
    List.Pairwise r (mergeSort r l) := by
  fun_induction mergeSort r l with
  | case1 => exact List.Pairwise.nil
  | case2 a => simp
  | case3 a b t ih1 ih2 =>
      exact pairwise_merge r htot htrans _ _ ih1 ih2

/-- **Mergesort is correct.**  For a total, transitive relation `r`, `mergeSort r l`
is a sorted (`List.Pairwise r`) permutation of the input list `l`. -/

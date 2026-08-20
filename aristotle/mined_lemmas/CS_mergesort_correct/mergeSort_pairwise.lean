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

variable {α : Type u}

/-- Merge two lists with respect to a boolean comparison `le`. -/

theorem mergeSort_pairwise (le : α → α → Bool)
    (htotal : ∀ a b, le a b || le b a) (htrans : ∀ a b c, le a b → le b c → le a c)
    (l : List α) : (mergeSort le l).Pairwise (fun a b => le a b = true) := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y t ih1 ih2 =>
      rw [mergeSort]
      exact merge_pairwise le htotal htrans ih1 ih2

/-- **Mergesort is correct**: for any total, transitive boolean comparison `le`,
`mergeSort le l` is a permutation of `l` which is sorted with respect to `le`. -/

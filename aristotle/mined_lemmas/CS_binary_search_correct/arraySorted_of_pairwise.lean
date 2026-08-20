import Mathlib

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Auxiliary binary search: looks for `k` in the index range `[lo, hi)` of the array `a`.
Returns `some i` when the key was found at index `i`, and `none` otherwise. -/

theorem arraySorted_of_pairwise {a : Array α} (h : a.toList.Pairwise (· ≤ ·)) :
    ArraySorted a := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have := (List.pairwise_iff_getElem.mp h) i j (by simpa using lt_of_le_of_lt hij hj)
      (by simpa using hj) hlt
    simpa using this

/-- Soundness: whenever the auxiliary search returns an index, the key sits at that index. -/

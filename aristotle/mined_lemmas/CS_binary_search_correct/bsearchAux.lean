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

def bsearchAux (a : Array α) (k : α) (lo hi : ℕ) : Option ℕ :=
  if lo < hi then
    match a[(lo + hi) / 2]? with
    | none => none
    | some x =>
        if x < k then bsearchAux a k ((lo + hi) / 2 + 1) hi
        else if k < x then bsearchAux a k lo ((lo + hi) / 2)
        else some ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search for `k` in the array `a`. -/

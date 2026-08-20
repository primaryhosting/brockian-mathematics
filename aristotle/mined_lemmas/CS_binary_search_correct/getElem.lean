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

namespace CS

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- Auxiliary binary search: looks for `k` in the index range `[lo, hi)` of the array `a`. -/

theorem getElem!_le_getElem!_of_sorted (a : Array α) (hs : a.toList.Pairwise (· ≤ ·))
    {p q : ℕ} (hpq : p ≤ q) (hq : q < a.size) : a[p]! ≤ a[q]! := by
  have hp : p < a.size := lt_of_le_of_lt hpq hq
  rw [getElem!_pos a p hp, getElem!_pos a q hq]
  have h := List.Pairwise.rel_get_of_le hs (a := ⟨p, by simpa using hp⟩)
      (b := ⟨q, by simpa using hq⟩) (by simpa using hpq)
  simpa using h

/-- Completeness of the auxiliary search on a sorted array: if the key occurs in the range
`[lo, hi)`, the search returns some index. -/

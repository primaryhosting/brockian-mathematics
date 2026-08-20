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

/-- Binary search for `key` in the sub-range `[lo, hi)` of the array `a`.
Returns `some i` for an index `i` with `a[i]! = key`, and `none` if the key is
not found in that range. -/

theorem binary_search_index (a : Array Int) (key : Int) (i : Nat)
    (h : binarySearch a key = some i) : i < a.size ∧ a[i]! = key := by
  obtain ⟨-, h2, h3⟩ := bsearchAux_sound a key 0 a.size i h
  exact ⟨h2, h3⟩

end CS


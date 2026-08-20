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

theorem bsearch_eq_some_iff_getElem (a : Array α) (k : α) (i : ℕ) (h : bsearch a k = some i) :
    ∃ hi : i < a.size, a[i] = k := by
  obtain ⟨_, hlt, heq⟩ := bsearchAux_sound a k 0 a.size i h
  exact ⟨hlt, by rw [← getElem!_pos a i hlt, heq]⟩

end CS


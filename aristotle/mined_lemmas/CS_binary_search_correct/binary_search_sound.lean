/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} [LT α] [DecidableLT α]

/-- Binary search for `key` in the index range `[lo, hi)` of the indexed collection `f`,
returning an index at which the key sits, if any. -/

theorem binary_search_sound [Inhabited α]
    (hconn : ∀ x y : α, ¬ x < y → ¬ y < x → x = y)
    (a : Array α) (key : α) (i : Nat) (h : binarySearch a key = some i) :
    ∃ hi : i < a.size, a[i] = key := by
  obtain ⟨-, hlt, heq⟩ := bsearchAux_sound hconn (fun i => a[i]!) key 0 a.size i h
  exact ⟨hlt, by rw [← heq, getElem!_pos a i hlt]⟩

end CS

import Mathlib
import RequestProject.CS

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

/-- Mathlib-facing corollary of `CS.binary_search_correct`: for an array over any
`LinearOrder` that is sorted (with respect to `≤`), `CS.binarySearch` returns an index
if and only if the key occurs in the array. -/

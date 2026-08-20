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

theorem bsearchAux_sound (a : Array α) (k : α) (lo hi i : ℕ)
    (h : bsearchAux a k lo hi = some i) : ∃ hi' : i < a.size, a[i] = k := by
  induction lo, hi using bsearchAux.induct (a := a) (k := k) generalizing i with
  | case1 lo hi hlt hnone =>
      rw [bsearchAux] at h
      simp [hlt, hnone] at h
  | case2 lo hi hlt x hx hxk ih =>
      rw [bsearchAux] at h
      simp only [hlt, hx, hxk, if_pos] at h
      exact ih _ h
  | case3 lo hi hlt x hx hxk hkx ih =>
      rw [bsearchAux] at h
      simp only [hlt, hx, hxk, hkx, if_pos, if_false] at h
      exact ih _ h
  | case4 lo hi hlt x hx hxk hkx =>
      rw [bsearchAux] at h
      simp only [hlt, hx, hxk, hkx, if_false] at h
      obtain rfl : (lo + hi) / 2 = i := Option.some.inj h
      obtain ⟨hlt', hval⟩ := Array.getElem?_eq_some_iff.mp hx
      refine ⟨hlt', ?_⟩
      have : x = k := le_antisymm (not_lt.mp hkx) (not_lt.mp hxk)
      rw [hval, this]
  | case5 lo hi hlt =>
      rw [bsearchAux] at h
      simp [hlt] at h

/-- Completeness: on a sorted array, if the key occurs at some index in `[lo, hi)` then the
auxiliary search succeeds. -/

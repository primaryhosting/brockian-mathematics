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

theorem bsearchAux_complete (a : Array α) (k : α) (hs : ArraySorted a) :
    ∀ (lo hi : ℕ) (hle : hi ≤ a.size) (i : ℕ), lo ≤ i → ∀ (hhi : i < hi),
      a[i]'(lt_of_lt_of_le hhi hle) = k → (bsearchAux a k lo hi).isSome := by
  intro lo hi
  induction lo, hi using bsearchAux.induct (a := a) (k := k) with
  | case1 lo hi hlt hnone =>
      intro hle i hlo hhi hik
      exfalso
      have : (lo + hi) / 2 < a.size := by omega
      rw [Array.getElem?_eq_none_iff] at hnone
      omega
  | case2 lo hi hlt x hx hxk ih =>
      intro hle i hlo hhi hik
      rw [bsearchAux]
      simp only [hlt, hx, hxk, if_pos]
      obtain ⟨hmid, hval⟩ := Array.getElem?_eq_some_iff.mp hx
      have hmi : (lo + hi) / 2 < i := by
        by_contra hcon
        push_neg at hcon
        have := hs i ((lo + hi) / 2) hcon hmid
        rw [hval, hik] at this
        exact absurd (lt_of_lt_of_le hxk this) (lt_irrefl x)
      exact ih hle i (by omega) hhi hik
  | case3 lo hi hlt x hx hxk hkx ih =>
      intro hle i hlo hhi hik
      rw [bsearchAux]
      simp only [hlt, hx, hxk, hkx, if_pos, if_false]
      obtain ⟨hmid, hval⟩ := Array.getElem?_eq_some_iff.mp hx
      have him : i < (lo + hi) / 2 := by
        by_contra hcon
        push_neg at hcon
        have := hs ((lo + hi) / 2) i hcon (by omega)
        rw [hval, hik] at this
        exact absurd (lt_of_lt_of_le hkx this) (lt_irrefl k)
      exact ih (by omega) i hlo him hik
  | case4 lo hi hlt x hx hxk hkx =>
      intro hle i hlo hhi hik
      rw [bsearchAux]
      simp only [hlt, hx, hxk, hkx, if_false]
      exact rfl
  | case5 lo hi hlt =>
      intro hle i hlo hhi hik
      omega

/-- **Binary search is correct.** On a sorted array, `binarySearch` returns an index if and only
if the key is present; moreover any index it returns is a genuine occurrence of the key. -/

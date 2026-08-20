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

theorem binary_search_correct (a : Array α) (k : α) (hs : a.toList.Pairwise (· ≤ ·)) :
    ((binarySearch a k).isSome ↔ k ∈ a) ∧
      ∀ (i : ℕ), binarySearch a k = some i → ∃ h : i < a.size, a[i] = k := by
  have hsort : ArraySorted a := arraySorted_of_pairwise hs
  have hsound : ∀ (i : ℕ), binarySearch a k = some i → ∃ h : i < a.size, a[i] = k := by
    intro i hi
    exact bsearchAux_sound a k 0 a.size i hi
  refine ⟨⟨?_, ?_⟩, hsound⟩
  · intro hsome
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hlt, hval⟩ := hsound i hi
    exact Array.mem_iff_getElem.mpr ⟨i, hlt, hval⟩
  · intro hmem
    obtain ⟨i, hlt, hval⟩ := Array.mem_iff_getElem.mp hmem
    exact bsearchAux_complete a k hsort 0 a.size (le_refl _) i (Nat.zero_le i) hlt hval

end CS


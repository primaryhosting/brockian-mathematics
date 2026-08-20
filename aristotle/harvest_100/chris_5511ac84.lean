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
def binarySearch (a : Array α) (k : α) : Option ℕ := bsearchAux a k 0 a.size

/-- Sortedness expressed via indices. -/
def ArraySorted (a : Array α) : Prop :=
  ∀ (i j : ℕ) (hij : i ≤ j) (hj : j < a.size), a[i]'(lt_of_le_of_lt hij hj) ≤ a[j]

theorem arraySorted_of_pairwise {a : Array α} (h : a.toList.Pairwise (· ≤ ·)) :
    ArraySorted a := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have := (List.pairwise_iff_getElem.mp h) i j (by simpa using lt_of_le_of_lt hij hj)
      (by simpa using hj) hlt
    simpa using this

/-- Soundness: whenever the auxiliary search returns an index, the key sits at that index. -/
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


/-
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- `Sorted a` says the array `a` is sorted in non-decreasing order. -/
def Sorted (a : Array α) : Prop :=
  ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!

/-- Binary search for `k` in the sub-range `[lo, hi)` of the array `a`.
Returns `some i` with `a[i]! = k` when found, and `none` otherwise. -/
def bsearchAux (a : Array α) (k : α) (lo hi : ℕ) : Option ℕ :=
  if lo < hi then
    if a[(lo + hi) / 2]! < k then bsearchAux a k ((lo + hi) / 2 + 1) hi
    else if k < a[(lo + hi) / 2]! then bsearchAux a k lo ((lo + hi) / 2)
    else some ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search of `k` in the whole array `a`. -/
def binarySearch (a : Array α) (k : α) : Option ℕ :=
  bsearchAux a k 0 a.size

/-- Soundness: any index returned by `bsearchAux` lies in the search range and
holds the key. -/
theorem bsearchAux_sound (a : Array α) (k : α) :
    ∀ lo hi i : ℕ, bsearchAux a k lo hi = some i → (lo ≤ i ∧ i < hi ∧ a[i]! = k) := by
  intro lo hi
  induction lo, hi using bsearchAux.induct (a := a) (k := k) with
  | case1 lo hi hlt hmid ih =>
      intro i hi'
      rw [bsearchAux] at hi'
      simp only [if_pos hlt, if_pos hmid] at hi'
      have := ih i hi'
      exact ⟨by omega, this.2.1, this.2.2⟩
  | case2 lo hi hlt hmid hmid2 ih =>
      intro i hi'
      rw [bsearchAux] at hi'
      simp only [if_pos hlt, if_neg hmid, if_pos hmid2] at hi'
      have := ih i hi'
      exact ⟨this.1, by omega, this.2.2⟩
  | case3 lo hi hlt hmid hmid2 =>
      intro i hi'
      rw [bsearchAux] at hi'
      simp only [if_pos hlt, if_neg hmid, if_neg hmid2, Option.some.injEq] at hi'
      subst hi'
      refine ⟨by omega, by omega, ?_⟩
      exact le_antisymm (not_lt.mp hmid2) (not_lt.mp hmid)
  | case4 lo hi hlt =>
      intro i hi'
      rw [bsearchAux] at hi'
      simp only [if_neg hlt] at hi'
      exact absurd hi' (by simp)

/-- Completeness: if the key occurs in the search range of a sorted array,
then `bsearchAux` finds some index. -/
theorem bsearchAux_complete (a : Array α) (hs : Sorted a) (k : α) :
    ∀ lo hi : ℕ, hi ≤ a.size → (∃ j, lo ≤ j ∧ j < hi ∧ a[j]! = k) →
      (bsearchAux a k lo hi).isSome := by
  intro lo hi
  induction lo, hi using bsearchAux.induct (a := a) (k := k) with
  | case1 lo hi hlt hmid ih =>
      rintro hsize ⟨j, hlo, hjhi, hj⟩
      rw [bsearchAux]
      simp only [if_pos hlt, if_pos hmid]
      refine ih hsize ⟨j, ?_, hjhi, hj⟩
      by_contra hcon
      have hjm : j ≤ (lo + hi) / 2 := by omega
      have : a[j]! ≤ a[(lo + hi) / 2]! := hs j ((lo + hi) / 2) hjm (by omega)
      rw [hj] at this
      exact absurd hmid (not_lt.mpr this)
  | case2 lo hi hlt hmid hmid2 ih =>
      rintro hsize ⟨j, hlo, hjhi, hj⟩
      rw [bsearchAux]
      simp only [if_pos hlt, if_neg hmid, if_pos hmid2]
      refine ih (by omega) ⟨j, hlo, ?_, hj⟩
      by_contra hcon
      have hmj : (lo + hi) / 2 ≤ j := by omega
      have : a[(lo + hi) / 2]! ≤ a[j]! := hs ((lo + hi) / 2) j hmj (by omega)
      rw [hj] at this
      exact absurd hmid2 (not_lt.mpr this)
  | case3 lo hi hlt hmid hmid2 =>
      intro _ _
      rw [bsearchAux]
      simp only [if_pos hlt, if_neg hmid, if_neg hmid2]
      rfl
  | case4 lo hi hlt =>
      rintro _ ⟨j, hlo, hjhi, _⟩
      omega

/-- **Binary search is correct.**  On a sorted array, `binarySearch` returns an
index if and only if the key is present; moreover any returned index is a valid
index holding the key. -/
theorem binary_search_correct (a : Array α) (hs : Sorted a) (k : α) :
    ((binarySearch a k).isSome ↔ ∃ i : ℕ, i < a.size ∧ a[i]! = k) ∧
      ∀ i : ℕ, binarySearch a k = some i → i < a.size ∧ a[i]! = k := by
  have hsound : ∀ i : ℕ, binarySearch a k = some i → i < a.size ∧ a[i]! = k := by
    intro i hi
    have := bsearchAux_sound a k 0 a.size i hi
    exact ⟨this.2.1, this.2.2⟩
  refine ⟨⟨?_, ?_⟩, hsound⟩
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
    exact ⟨i, hsound i hi⟩
  · rintro ⟨i, hi, hik⟩
    exact bsearchAux_complete a hs k 0 a.size le_rfl ⟨i, Nat.zero_le _, hi, hik⟩

end CS


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
def bsearchAux (a : Array α) (k : α) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if a[mid]! < k then bsearchAux a k (mid + 1) hi
    else if k < a[mid]! then bsearchAux a k lo mid
    else some mid
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search for `k` in the array `a`, returning `some i` with `a[i] = k` if found. -/
def bsearch (a : Array α) (k : α) : Option ℕ := bsearchAux a k 0 a.size

/-- Soundness of the auxiliary search: any returned index lies in `[lo, hi)` and holds the key.
No sortedness assumption is needed here. -/
theorem bsearchAux_sound (a : Array α) (k : α) (lo hi i : ℕ)
    (h : bsearchAux a k lo hi = some i) : lo ≤ i ∧ i < hi ∧ a[i]! = k := by
  induction lo, hi using CS.bsearchAux.induct (a := a) (k := k) with
  | case1 lo hi hlt mid hmid ih =>
      rw [bsearchAux, dif_pos hlt, if_pos hmid] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, h2, h3⟩
  | case2 lo hi hlt mid h1 h2 ih =>
      rw [bsearchAux, dif_pos hlt, if_neg h1, if_pos h2] at h
      obtain ⟨k1, k2, k3⟩ := ih h
      exact ⟨k1, by omega, k3⟩
  | case3 lo hi hlt mid h1 h2 =>
      rw [bsearchAux, dif_pos hlt, if_neg h1, if_neg h2] at h
      have him : i = mid := by simpa [eq_comm] using h
      subst him
      exact ⟨by omega, by omega, le_antisymm (not_lt.mp h2) (not_lt.mp h1)⟩
  | case4 lo hi hlt =>
      rw [bsearchAux, dif_neg hlt] at h
      exact absurd h (by simp)

/-- Pointwise monotonicity of a sorted array. -/
theorem getElem!_le_getElem!_of_sorted (a : Array α) (hs : a.toList.Pairwise (· ≤ ·))
    {p q : ℕ} (hpq : p ≤ q) (hq : q < a.size) : a[p]! ≤ a[q]! := by
  have hp : p < a.size := lt_of_le_of_lt hpq hq
  rw [getElem!_pos a p hp, getElem!_pos a q hq]
  have h := List.Pairwise.rel_get_of_le hs (a := ⟨p, by simpa using hp⟩)
      (b := ⟨q, by simpa using hq⟩) (by simpa using hpq)
  simpa using h

/-- Completeness of the auxiliary search on a sorted array: if the key occurs in the range
`[lo, hi)`, the search returns some index. -/
theorem bsearchAux_complete (a : Array α) (k : α) (hs : a.toList.Pairwise (· ≤ ·)) :
    ∀ lo hi : ℕ, hi ≤ a.size → (∃ i, lo ≤ i ∧ i < hi ∧ a[i]! = k) →
      ∃ j, bsearchAux a k lo hi = some j := by
  intro lo hi
  induction lo, hi using CS.bsearchAux.induct (a := a) (k := k) with
  | case1 lo hi hlt mid hmid ih =>
      intro hhi hex
      obtain ⟨i, hlo, hih, hik⟩ := hex
      have hmidlt : mid < hi := by simp only [mid]; omega
      have hmi : mid < i := by
        by_contra hc
        have : a[i]! ≤ a[mid]! :=
          getElem!_le_getElem!_of_sorted a hs (not_lt.mp hc) (lt_of_lt_of_le hmidlt hhi)
        rw [hik] at this
        exact absurd hmid (not_lt.mpr this)
      rw [bsearchAux, dif_pos hlt, if_pos hmid]
      exact ih hhi ⟨i, by omega, hih, hik⟩
  | case2 lo hi hlt mid h1 h2 ih =>
      intro hhi hex
      obtain ⟨i, hlo, hih, hik⟩ := hex
      have hmidlt : mid < hi := by simp only [mid]; omega
      have him : i < mid := by
        by_contra hc
        have : a[mid]! ≤ a[i]! :=
          getElem!_le_getElem!_of_sorted a hs (not_lt.mp hc) (lt_of_lt_of_le hih hhi)
        rw [hik] at this
        exact absurd h2 (not_lt.mpr this)
      rw [bsearchAux, dif_pos hlt, if_neg h1, if_pos h2]
      exact ih (le_of_lt (lt_of_lt_of_le hmidlt hhi)) ⟨i, hlo, him, hik⟩
  | case3 lo hi hlt mid h1 h2 =>
      intro _ _
      rw [bsearchAux, dif_pos hlt, if_neg h1, if_neg h2]
      exact ⟨mid, rfl⟩
  | case4 lo hi hlt =>
      intro _ hex
      obtain ⟨i, hlo, hih, _⟩ := hex
      omega

/-- **Binary search is correct**: on a sorted array, `bsearch` returns an index if and only if
the key occurs in the array. -/
theorem binary_search_correct (a : Array α) (k : α) (hs : a.toList.Pairwise (· ≤ ·)) :
    (∃ i, bsearch a k = some i) ↔ k ∈ a := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨_, hlt, heq⟩ := bsearchAux_sound a k 0 a.size i hi
    rw [Array.mem_iff_getElem]
    exact ⟨i, hlt, by rw [← getElem!_pos a i hlt, heq]⟩
  · intro hk
    rw [Array.mem_iff_getElem] at hk
    obtain ⟨i, hlt, heq⟩ := hk
    exact bsearchAux_complete a k hs 0 a.size le_rfl
      ⟨i, Nat.zero_le i, hlt, by rw [getElem!_pos a i hlt, heq]⟩

/-- The index returned by `bsearch` is a valid index holding the key. -/
theorem bsearch_eq_some_iff_getElem (a : Array α) (k : α) (i : ℕ) (h : bsearch a k = some i) :
    ∃ hi : i < a.size, a[i] = k := by
  obtain ⟨_, hlt, heq⟩ := bsearchAux_sound a k 0 a.size i h
  exact ⟨hlt, by rw [← getElem!_pos a i hlt, heq]⟩

end CS


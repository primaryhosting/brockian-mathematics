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
def bsearchAux (f : Nat → α) (key : α) (lo hi : Nat) : Option Nat :=
  if lo < hi then
    if f ((lo + hi) / 2) < key then bsearchAux f key ((lo + hi) / 2 + 1) hi
    else if key < f ((lo + hi) / 2) then bsearchAux f key lo ((lo + hi) / 2)
    else some ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Soundness: if `bsearchAux` returns an index, that index lies in the search range and
the collection really holds `key` there.  No sortedness assumption is needed; the only
property of the order that is used is connectedness (`hconn`), which holds in any
linear order. -/
theorem bsearchAux_sound (hconn : ∀ x y : α, ¬ x < y → ¬ y < x → x = y)
    (f : Nat → α) (key : α) (lo hi i : Nat)
    (h : bsearchAux f key lo hi = some i) : lo ≤ i ∧ i < hi ∧ f i = key := by
  induction lo, hi using bsearchAux.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchAux, if_pos hlt, if_pos hmid] at h
      have hih := ih h
      exact ⟨by omega, hih.2.1, hih.2.2⟩
  | case2 lo hi hlt hmid hlt2 ih =>
      rw [bsearchAux, if_pos hlt, if_neg hmid, if_pos hlt2] at h
      have hih := ih h
      exact ⟨hih.1, by omega, hih.2.2⟩
  | case3 lo hi hlt hmid hlt2 =>
      rw [bsearchAux, if_pos hlt, if_neg hmid, if_neg hlt2, Option.some.injEq] at h
      subst h
      exact ⟨by omega, by omega, hconn _ _ hmid hlt2⟩
  | case4 lo hi hlt =>
      rw [bsearchAux, if_neg hlt] at h
      exact absurd h (by simp)

/-- Completeness: if the range `[lo, hi)` is sorted and the key occurs in it, then
`bsearchAux` returns an index. -/
theorem bsearchAux_complete (f : Nat → α) (key : α) (lo hi : Nat)
    (hsorted : ∀ i j : Nat, i ≤ j → j < hi → ¬ (f j < f i)) (i : Nat)
    (hlo : lo ≤ i) (hhi : i < hi) (hfi : f i = key) :
    (bsearchAux f key lo hi).isSome := by
  induction lo, hi using bsearchAux.induct (f := f) (key := key) generalizing i with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchAux, if_pos hlt, if_pos hmid]
      refine ih hsorted i ?_ hhi hfi
      refine Nat.not_lt.mp (fun hcon => ?_)
      have h1 : ¬ (f ((lo + hi) / 2) < f i) := hsorted i ((lo + hi) / 2) (by omega) (by omega)
      rw [hfi] at h1
      exact h1 hmid
  | case2 lo hi hlt hmid hlt2 ih =>
      rw [bsearchAux, if_pos hlt, if_neg hmid, if_pos hlt2]
      refine ih (fun a b hab hb => hsorted a b hab (by omega)) i hlo ?_ hfi
      refine Nat.not_le.mp (fun hcon => ?_)
      have h1 : ¬ (f i < f ((lo + hi) / 2)) := hsorted ((lo + hi) / 2) i (by omega) hhi
      rw [hfi] at h1
      exact h1 hlt2
  | case3 lo hi hlt hmid hlt2 =>
      rw [bsearchAux, if_pos hlt, if_neg hmid, if_neg hlt2]
      rfl
  | case4 lo hi hlt =>
      omega

/-- Binary search on an array. -/
def binarySearch [Inhabited α] (a : Array α) (key : α) : Option Nat :=
  bsearchAux (fun i => a[i]!) key 0 a.size

/-- **Binary search is correct**: on a sorted array, `binarySearch` returns an index
if and only if the key occurs in the array.

The order is only assumed to be a decidable `<` satisfying connectedness `hconn`
(`¬ x < y → ¬ y < x → x = y`), which every linear order satisfies. -/
theorem binary_search_correct [Inhabited α]
    (hconn : ∀ x y : α, ¬ x < y → ¬ y < x → x = y)
    (a : Array α) (key : α)
    (hsorted : ∀ i j : Nat, i ≤ j → j < a.size → ¬ (a[j]! < a[i]!)) :
    (binarySearch a key).isSome ↔ key ∈ a := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨-, hlt, heq⟩ := bsearchAux_sound hconn (fun i => a[i]!) key 0 a.size i hi
    rw [Array.mem_iff_getElem]
    exact ⟨i, hlt, by rw [← heq, getElem!_pos a i hlt]⟩
  · intro h
    rw [Array.mem_iff_getElem] at h
    obtain ⟨i, hlt, heq⟩ := h
    refine bsearchAux_complete (fun i => a[i]!) key 0 a.size hsorted i (Nat.zero_le _) hlt ?_
    simpa [getElem!_pos a i hlt] using heq

/-- Soundness of `binarySearch`: the returned index is in bounds and holds the key. -/
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
theorem binary_search_correct_of_linearOrder {α : Type*} [LinearOrder α] [Inhabited α]
    (a : Array α) (key : α)
    (hsorted : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    (CS.binarySearch a key).isSome ↔ key ∈ a :=
  CS.binary_search_correct
    (fun _ _ hxy hyx => le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)) a key
    (fun i j hij hj => not_lt.mpr (hsorted i j hij hj))

end CS

-- Sanity checks.
example : CS.binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by
  simp [CS.binarySearch, CS.bsearchAux]
example : CS.binarySearch #[1, 3, 5, 7, 9] 4 = none := by
  simp [CS.binarySearch, CS.bsearchAux]

#print axioms CS.binary_search_correct


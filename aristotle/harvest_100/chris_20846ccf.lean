import Mathlib
import RequestProject.Main

/-!
# Binary search correctness, specialised to a Mathlib `LinearOrder`

`CS.binary_search_correct` (in `RequestProject.Main`) is stated for an arbitrary decidable
strict order satisfying antisymmetry.  Here we record the corollary for any Mathlib
`LinearOrder`, where the antisymmetry hypothesis is automatic, and we phrase sortedness
using `≤`.
-/

namespace CS

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- Sortedness stated with `≤` agrees with `CS.Sorted`. -/
theorem sorted_iff_le (a : Array α) :
    Sorted a ↔ ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]! := by
  constructor
  · intro h i j hij hj
    exact not_lt.mp (h i j hij hj)
  · intro h i j hij hj
    exact not_lt.mpr (h i j hij hj)

/-- **Binary search is correct** over any linear order: on a sorted array, `binarySearch`
returns an index iff the key occurs in the array, and any returned index is a valid index
carrying the key. -/
theorem binary_search_correct_linearOrder (a : Array α)
    (hs : ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]!) (key : α) :
    (∀ i : Nat, binarySearch a key = some i → i < a.size ∧ a[i]! = key) ∧
      ((∃ i : Nat, binarySearch a key = some i) ↔ ∃ i : Nat, i < a.size ∧ a[i]! = key) :=
  binary_search_correct (fun _ _ h1 h2 => le_antisymm (not_lt.mp h2) (not_lt.mp h1)) a
    ((sorted_iff_le a).mpr hs) key

/-- A concrete sanity check. -/
example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by
  simp [binarySearch, bsearchAux]

example : binarySearch #[1, 3, 5, 7, 9] 4 = none := by
  simp [binarySearch, bsearchAux]

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-!
## Setup

We work with an arbitrary type `α` carrying a decidable strict order `<`.  The only order
property that binary search needs is antisymmetry in the form

`∀ x y, ¬ x < y → ¬ y < x → x = y`,

which holds in any linear order; it is supplied as an explicit hypothesis so that the
development is independent of any particular order-class hierarchy.
-/

variable {α : Type u} [LT α] [DecidableLT α] [Inhabited α]

/-- An array is sorted when its entries are non-decreasing, i.e. `a[i]! ≤ a[j]!` for `i ≤ j`,
expressed with the strict order as `¬ a[j]! < a[i]!`. -/
def Sorted (a : Array α) : Prop :=
  ∀ i j : Nat, i ≤ j → j < a.size → ¬ (a[j]! < a[i]!)

/-- The recursive core of binary search: look for `key` inside the index window `[lo, hi)`. -/
def bsearchAux (a : Array α) (key : α) (lo hi : Nat) : Option Nat :=
  if lo < hi then
    if a[(lo + hi) / 2]! < key then bsearchAux a key ((lo + hi) / 2 + 1) hi
    else if key < a[(lo + hi) / 2]! then bsearchAux a key lo ((lo + hi) / 2)
    else some ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search for `key` in the array `a`. -/
def binarySearch (a : Array α) (key : α) : Option Nat :=
  bsearchAux a key 0 a.size

/-- **Soundness of the recursive core.**  Any index returned by `bsearchAux` lies in the
search window `[lo, hi)` and its entry is exactly `key`.  Sortedness is not needed here. -/
theorem bsearchAux_sound (hanti : ∀ x y : α, ¬ x < y → ¬ y < x → x = y)
    (a : Array α) (key : α) :
    ∀ lo hi i : Nat, bsearchAux a key lo hi = some i → lo ≤ i ∧ i < hi ∧ a[i]! = key := by
  intro lo hi
  induction lo, hi using bsearchAux.induct a key with
  | case1 lo hi hlt hmid ih =>
      intro i hres
      rw [bsearchAux, if_pos hlt, if_pos hmid] at hres
      have h := ih i hres
      exact ⟨by omega, h.2.1, h.2.2⟩
  | case2 lo hi hlt hmid1 hmid2 ih =>
      intro i hres
      rw [bsearchAux, if_pos hlt, if_neg hmid1, if_pos hmid2] at hres
      have h := ih i hres
      exact ⟨h.1, by omega, h.2.2⟩
  | case3 lo hi hlt hmid1 hmid2 =>
      intro i hres
      rw [bsearchAux, if_pos hlt, if_neg hmid1, if_neg hmid2] at hres
      have hi' : i = (lo + hi) / 2 := (Option.some.inj hres).symm
      subst hi'
      exact ⟨by omega, by omega, hanti _ _ hmid1 hmid2⟩
  | case4 lo hi hlt =>
      intro i hres
      rw [bsearchAux, if_neg hlt] at hres
      exact absurd hres (by simp)

/-- **Completeness of the recursive core.**  If a sorted array contains `key` at some index
inside the window `[lo, hi)`, then the search succeeds. -/
theorem bsearchAux_complete (a : Array α) (hs : Sorted a) (key : α) :
    ∀ lo hi : Nat, hi ≤ a.size → ∀ j : Nat, lo ≤ j → j < hi → a[j]! = key →
      (bsearchAux a key lo hi).isSome := by
  intro lo hi
  induction lo, hi using bsearchAux.induct a key with
  | case1 lo hi hlt hmid ih =>
      intro hsize j hlo hj hkey
      have hmidlt : (lo + hi) / 2 < a.size := by omega
      have hjmid : (lo + hi) / 2 < j :=
        match Nat.lt_or_ge ((lo + hi) / 2) j with
        | Or.inl h => h
        | Or.inr h => absurd hmid (hkey ▸ hs j ((lo + hi) / 2) h hmidlt)
      rw [bsearchAux, if_pos hlt, if_pos hmid]
      exact ih hsize j (by omega) hj hkey
  | case2 lo hi hlt hmid1 hmid2 ih =>
      intro hsize j hlo hj hkey
      have hjmid : j < (lo + hi) / 2 :=
        match Nat.lt_or_ge j ((lo + hi) / 2) with
        | Or.inl h => h
        | Or.inr h => absurd hmid2 (hkey ▸ hs ((lo + hi) / 2) j h (by omega))
      rw [bsearchAux, if_pos hlt, if_neg hmid1, if_pos hmid2]
      exact ih (by omega) j hlo hjmid hkey
  | case3 lo hi hlt hmid1 hmid2 =>
      intro _ _ _ _ _
      rw [bsearchAux, if_pos hlt, if_neg hmid1, if_neg hmid2]
      rfl
  | case4 lo hi hlt =>
      intro _ j _ hj _
      omega

/--
**Binary search is correct.**

For a sorted array `a` over a type with a decidable antisymmetric strict order, and a key
`key`:

* (soundness) every index returned by `binarySearch a key` is a valid index of `a` whose
  entry equals `key`;
* (completeness) `binarySearch a key` returns an index **iff** `key` occurs in `a`.
-/
theorem binary_search_correct (hanti : ∀ x y : α, ¬ x < y → ¬ y < x → x = y)
    (a : Array α) (hs : Sorted a) (key : α) :
    (∀ i : Nat, binarySearch a key = some i → i < a.size ∧ a[i]! = key) ∧
      ((∃ i : Nat, binarySearch a key = some i) ↔ ∃ i : Nat, i < a.size ∧ a[i]! = key) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hres
    have h := bsearchAux_sound hanti a key 0 a.size i hres
    exact ⟨h.2.1, h.2.2⟩
  · rintro ⟨i, hres⟩
    have h := bsearchAux_sound hanti a key 0 a.size i hres
    exact ⟨i, h.2.1, h.2.2⟩
  · rintro ⟨j, hj, hkey⟩
    have h := bsearchAux_complete a hs key 0 a.size (Nat.le_refl _) j (Nat.zero_le _) hj hkey
    exact Option.isSome_iff_exists.mp h

end CS


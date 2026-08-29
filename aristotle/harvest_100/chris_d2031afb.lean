import Mathlib

/-!
# Binary search over an arbitrary linear order (Mathlib version)

This is the same development as in `RequestProject/Main.lean`, but for arrays over an
arbitrary `LinearOrder`.  The main result is `CS.binary_search_correct_general`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`. -/
def bsearchRangeGen (f : ℕ → α) (key : α) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi then
    if f ((lo + hi) / 2) < key then
      bsearchRangeGen f key ((lo + hi) / 2 + 1) hi
    else if key < f ((lo + hi) / 2) then
      bsearchRangeGen f key lo ((lo + hi) / 2)
    else
      some ((lo + hi) / 2)
  else
    none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- If binary search returns an index, that index lies in the search range and the array
really holds `key` there. -/
theorem bsearchRangeGen_eq_some {f : ℕ → α} {key : α} {lo hi i : ℕ}
    (h : bsearchRangeGen f key lo hi = some i) : lo ≤ i ∧ i < hi ∧ f i = key := by
  induction lo, hi using bsearchRangeGen.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchRangeGen, dif_pos hlt, if_pos hmid] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, h2, h3⟩
  | case2 lo hi hlt hmid hmid' ih =>
      rw [bsearchRangeGen, dif_pos hlt, if_neg hmid, if_pos hmid'] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨h1, by omega, h3⟩
  | case3 lo hi hlt hmid hmid' =>
      rw [bsearchRangeGen, dif_pos hlt, if_neg hmid, if_neg hmid'] at h
      have hi' : (lo + hi) / 2 = i := Option.some.inj h
      refine ⟨by omega, by omega, ?_⟩
      rw [← hi']
      exact le_antisymm (not_lt.mp hmid') (not_lt.mp hmid)
  | case4 lo hi hlt =>
      rw [bsearchRangeGen, dif_neg hlt] at h
      exact absurd h (by simp)

/-- If binary search fails on a sorted range, the key does not occur in that range. -/
theorem bsearchRangeGen_eq_none {f : ℕ → α} {key : α} {lo hi : ℕ}
    (hs : ∀ i j, i ≤ j → j < hi → f i ≤ f j)
    (h : bsearchRangeGen f key lo hi = none) :
    ∀ i, lo ≤ i → i < hi → f i ≠ key := by
  induction lo, hi using bsearchRangeGen.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchRangeGen, dif_pos hlt, if_pos hmid] at h
      intro i hi1 hi2 heq
      by_cases hle : i ≤ (lo + hi) / 2
      · have hle' : f i ≤ f ((lo + hi) / 2) := hs i _ hle (by omega)
        rw [heq] at hle'
        exact absurd (lt_of_le_of_lt hle' hmid) (lt_irrefl _)
      · exact ih hs h i (by omega) hi2 heq
  | case2 lo hi hlt hmid hmid' ih =>
      rw [bsearchRangeGen, dif_pos hlt, if_neg hmid, if_pos hmid'] at h
      have hs' : ∀ i j, i ≤ j → j < (lo + hi) / 2 → f i ≤ f j :=
        fun i j hij hj => hs i j hij (by omega)
      intro i hi1 hi2 heq
      by_cases hlt' : i < (lo + hi) / 2
      · exact ih hs' h i hi1 hlt' heq
      · have hge' : f ((lo + hi) / 2) ≤ f i := hs _ i (by omega) hi2
        rw [heq] at hge'
        exact absurd (lt_of_lt_of_le hmid' hge') (lt_irrefl _)
  | case3 lo hi hlt hmid hmid' =>
      rw [bsearchRangeGen, dif_pos hlt, if_neg hmid, if_neg hmid'] at h
      exact absurd h (by simp)
  | case4 lo hi hlt =>
      intro i hi1 hi2
      omega

/-- Binary search over a whole array. -/
def arrayBSearchGen [Inhabited α] (a : Array α) (key : α) : Option ℕ :=
  bsearchRangeGen (fun i => a[i]!) key 0 a.size

/-- **Binary search is correct** (general version).  On a sorted array over an arbitrary
linear order, binary search returns an index iff the key is present in the array; and any
returned index is a valid index at which the key really occurs. -/
theorem binary_search_correct_general [Inhabited α] (a : Array α) (key : α)
    (hsorted : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    ((∃ i, arrayBSearchGen a key = some i) ↔ ∃ i, i < a.size ∧ a[i]! = key) ∧
      ∀ i, arrayBSearchGen a key = some i → i < a.size ∧ a[i]! = key := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3⟩ := bsearchRangeGen_eq_some hi
    exact ⟨i, h2, h3⟩
  · rintro ⟨i, hi1, hi2⟩
    rcases hnone : arrayBSearchGen a key with _ | j
    · exact absurd hi2 (bsearchRangeGen_eq_none hsorted hnone i (Nat.zero_le _) hi1)
    · exact ⟨j, rfl⟩
  · intro i hi
    obtain ⟨-, h2, h3⟩ := bsearchRangeGen_eq_some hi
    exact ⟨h2, h3⟩

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean 4 module docstring (`/-! ... -/`) must be the first *command* in a
file, and `import` commands must precede every other command.  Since the required header above
is a module docstring, this file cannot contain any `import` line, so the development below is
carried out over `Int` using only the Lean 4 core library.  A fully general Mathlib version, for
an arbitrary `LinearOrder`, is proved in `RequestProject/BinarySearchGeneral.lean` as
`CS.binary_search_correct_general`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`.
Returns `some i` (with `f i = key`) if the key is found there, and `none` otherwise. -/
def bsearchRange (f : Nat → Int) (key : Int) (lo hi : Nat) : Option Nat :=
  if h : lo < hi then
    if f ((lo + hi) / 2) < key then
      bsearchRange f key ((lo + hi) / 2 + 1) hi
    else if key < f ((lo + hi) / 2) then
      bsearchRange f key lo ((lo + hi) / 2)
    else
      some ((lo + hi) / 2)
  else
    none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- If binary search returns an index, that index lies in the search range and the
array really holds `key` there.  (No sortedness assumption is needed for this direction.) -/
theorem bsearchRange_eq_some {f : Nat → Int} {key : Int} {lo hi i : Nat}
    (h : bsearchRange f key lo hi = some i) : lo ≤ i ∧ i < hi ∧ f i = key := by
  induction lo, hi using bsearchRange.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchRange, dif_pos hlt, if_pos hmid] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, h2, h3⟩
  | case2 lo hi hlt hmid hmid' ih =>
      rw [bsearchRange, dif_pos hlt, if_neg hmid, if_pos hmid'] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨h1, by omega, h3⟩
  | case3 lo hi hlt hmid hmid' =>
      rw [bsearchRange, dif_pos hlt, if_neg hmid, if_neg hmid'] at h
      have hi' : (lo + hi) / 2 = i := Option.some.inj h
      refine ⟨by omega, by omega, ?_⟩
      rw [← hi']
      omega
  | case4 lo hi hlt =>
      rw [bsearchRange, dif_neg hlt] at h
      exact absurd h (by simp)

/-- If binary search fails on a sorted range, then the key does not occur in that range. -/
theorem bsearchRange_eq_none {f : Nat → Int} {key : Int} {lo hi : Nat}
    (hs : ∀ i j, i ≤ j → j < hi → f i ≤ f j)
    (h : bsearchRange f key lo hi = none) :
    ∀ i, lo ≤ i → i < hi → f i ≠ key := by
  induction lo, hi using bsearchRange.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid ih =>
      rw [bsearchRange, dif_pos hlt, if_pos hmid] at h
      intro i hi1 hi2 heq
      by_cases hle : i ≤ (lo + hi) / 2
      · have hle' : f i ≤ f ((lo + hi) / 2) := hs i _ hle (by omega)
        omega
      · exact ih hs h i (by omega) hi2 heq
  | case2 lo hi hlt hmid hmid' ih =>
      rw [bsearchRange, dif_pos hlt, if_neg hmid, if_pos hmid'] at h
      have hs' : ∀ i j, i ≤ j → j < (lo + hi) / 2 → f i ≤ f j :=
        fun i j hij hj => hs i j hij (by omega)
      intro i hi1 hi2 heq
      by_cases hlt' : i < (lo + hi) / 2
      · exact ih hs' h i hi1 hlt' heq
      · have hge' : f ((lo + hi) / 2) ≤ f i := hs _ i (by omega) hi2
        omega
  | case3 lo hi hlt hmid hmid' =>
      rw [bsearchRange, dif_pos hlt, if_neg hmid, if_neg hmid'] at h
      exact absurd h (by simp)
  | case4 lo hi hlt =>
      intro i hi1 hi2
      omega

/-- Binary search over a whole array. -/
def arrayBSearch (a : Array Int) (key : Int) : Option Nat :=
  bsearchRange (fun i => a[i]!) key 0 a.size

/-- **Binary search is correct.**  On a sorted array, binary search returns an index if and
only if the key is present in the array; moreover, whenever it returns an index, that index is
a valid index of the array at which the key really occurs. -/
theorem binary_search_correct (a : Array Int) (key : Int)
    (hsorted : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    ((∃ i, arrayBSearch a key = some i) ↔ ∃ i, i < a.size ∧ a[i]! = key) ∧
      ∀ i, arrayBSearch a key = some i → i < a.size ∧ a[i]! = key := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3⟩ := bsearchRange_eq_some hi
    exact ⟨i, h2, h3⟩
  · rintro ⟨i, hi1, hi2⟩
    rcases hnone : arrayBSearch a key with _ | j
    · exact absurd hi2 (bsearchRange_eq_none hsorted hnone i (Nat.zero_le _) hi1)
    · exact ⟨j, rfl⟩
  · intro i hi
    obtain ⟨-, h2, h3⟩ := bsearchRange_eq_some hi
    exact ⟨h2, h3⟩

end CS


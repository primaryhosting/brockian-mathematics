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

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

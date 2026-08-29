import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

lemma sum_Icc_succ_succ (u v : ℕ) :
    ∑ i ∈ Finset.Icc (u + 1) (v + 1), i
      = (∑ i ∈ Finset.Icc u v, i) + (Finset.Icc u v).card := by
  rw [← Finset.image_add_right_Icc u v 1,
    Finset.sum_image (by intro x _ y _ h; simpa using h)]
  simp [Finset.sum_add_distrib]


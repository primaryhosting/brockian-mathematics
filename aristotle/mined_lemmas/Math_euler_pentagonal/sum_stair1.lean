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

lemma sum_stair1 (k : ℕ) : 2 * ∑ i ∈ Finset.Ico k (2 * k), i = k * (3 * k - 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * k - k = k := by omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  cases k with
  | zero => simp
  | succ m =>
    have hs := Finset.sum_range_id_mul_two (m + 1)
    simp only [Nat.add_sub_cancel] at hs
    have h3 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    rw [h3]
    nlinarith [hs]


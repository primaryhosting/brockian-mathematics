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

lemma op1_card (h0 : 0 ∉ s) (hA : IsA s) : (op1 s).card + 1 = s.card := by
  conv_rhs => rw [decompA hA]
  rw [Finset.card_insert_of_notMem (mn_notMemA h0 hA), Finset.card_union_of_disjoint disjA1,
    op1_eq, Finset.card_union_of_disjoint disjA2, card_IccA h0 hA, card_IccA' h0 hA]


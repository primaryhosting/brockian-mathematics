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

lemma op2_card (h0 : 0 ∉ t) (hB : IsB t) : (op2 t).card = t.card + 1 := by
  conv_rhs => rw [decompB hB.1]
  rw [op2_eq, Finset.card_insert_of_notMem (run_notMemB h0 hB),
    Finset.card_union_of_disjoint (disjB2 h0), Finset.card_union_of_disjoint (disjB1 h0),
    card_IccB h0 hB, card_Icc_run hB.1 h0]


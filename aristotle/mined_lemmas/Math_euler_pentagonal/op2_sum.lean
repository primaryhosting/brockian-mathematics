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

lemma op2_sum (h0 : 0 ∉ t) (hB : IsB t) : ∑ i ∈ op2 t, i = ∑ i ∈ t, i := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have hshift : ∑ i ∈ Finset.Icc (mx t - run t + 1) (mx t), i
      = (∑ i ∈ Finset.Icc (mx t - run t) (mx t - 1), i) + run t := by
    have h3 : mx t = (mx t - 1) + 1 := by omega
    rw [show Finset.Icc (mx t - run t + 1) (mx t)
        = Finset.Icc ((mx t - run t) + 1) ((mx t - 1) + 1) by rw [← h3],
      sum_Icc_succ_succ, card_IccB h0 hB]
  conv_rhs => rw [decompB hB.1]
  rw [op2_eq, Finset.sum_insert (run_notMemB h0 hB), Finset.sum_union (disjB2 h0),
    Finset.sum_union (disjB1 h0), hshift]
  omega


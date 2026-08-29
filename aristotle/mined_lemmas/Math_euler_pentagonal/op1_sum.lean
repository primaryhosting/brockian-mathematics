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

lemma op1_sum (h0 : 0 ∉ s) (hA : IsA s) : ∑ i ∈ op1 s, i = ∑ i ∈ s, i := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hshift : ∑ i ∈ Finset.Icc (mx s - mn s + 2) (mx s + 1), i
      = (∑ i ∈ Finset.Icc (mx s - mn s + 1) (mx s), i) + mn s := by
    have h2 : mx s - mn s + 2 = (mx s - mn s + 1) + 1 := by omega
    rw [h2, sum_Icc_succ_succ, card_IccA h0 hA]
  conv_rhs => rw [decompA hA]
  rw [Finset.sum_insert (mn_notMemA h0 hA), Finset.sum_union disjA1, op1_eq,
    Finset.sum_union disjA2, hshift]
  omega


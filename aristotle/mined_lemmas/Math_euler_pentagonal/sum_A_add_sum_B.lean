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

lemma sum_A_add_sum_B (n : ℕ) :
    (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ (DP n).filter IsB, (-1 : ℤ) ^ s.card = 0 := by
  have key : (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      = ∑ t ∈ (DP n).filter IsB, (-((-1 : ℤ) ^ t.card)) := by
    refine Finset.sum_nbij' op1 op2 ?_ ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      obtain ⟨⟨h0, hsum⟩, hA⟩ := hs
      rw [Finset.mem_filter, mem_DP]
      exact ⟨⟨op1_zero_notMem h0 hA, by rw [op1_sum h0 hA, hsum]⟩, op1_isB h0 hA⟩
    · intro t ht
      rw [Finset.mem_filter, mem_DP] at ht
      obtain ⟨⟨h0, hsum⟩, hB⟩ := ht
      rw [Finset.mem_filter, mem_DP]
      exact ⟨⟨op2_zero_notMem h0 hB, by rw [op2_sum h0 hB, hsum]⟩, op2_isA h0 hB⟩
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      exact op2_op1 hs.1.1 hs.2
    · intro t ht
      rw [Finset.mem_filter, mem_DP] at ht
      exact op1_op2 ht.1.1 ht.2
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      obtain ⟨⟨h0, hsum⟩, hA⟩ := hs
      have hc := op1_card h0 hA
      rw [← hc, pow_succ]
      ring
  rw [key, Finset.sum_neg_distrib, neg_add_cancel]

end Cancellation

end Moves

section Exceptional

/-- The signed count of generalized pentagonal representations of `n`: the coefficient of `X^n`
in `∑ k, (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`. -/

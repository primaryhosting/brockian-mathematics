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

private lemma prod_fsgn (n : ℕ) (p : n.Partition) :
    p.parts.toFinsupp.prod fsgn = if p.parts.Nodup then (-1 : ℤ) ^ (Multiset.card p.parts) else 0 := by
  rw [Finsupp.prod]
  simp only [Multiset.toFinsupp_support, Multiset.toFinsupp_apply, fsgn]
  by_cases h : p.parts.Nodup
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun i hi => if_pos (by
      rw [Multiset.nodup_iff_count_eq_one] at h
      exact h i (Multiset.mem_toFinset.mp hi)))]
    rw [Finset.prod_const, Multiset.toFinset_card_of_nodup h]
  · rw [if_neg h]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (i := i) ?_ ?_
    · exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega))
    · exact if_neg (by omega)

/-- Signed counting of distinct partitions, transported from `Finset ℕ` to `Nat.Partition`. -/

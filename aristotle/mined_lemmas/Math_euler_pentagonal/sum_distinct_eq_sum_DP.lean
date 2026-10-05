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

private lemma sum_distinct_eq_sum_DP (n : ℕ) :
    ∑ p ∈ (univ.filter (fun p : n.Partition => p.parts.Nodup)), (-1 : ℤ) ^ (Multiset.card p.parts)
      = ∑ s ∈ Franklin.DP n, (-1 : ℤ) ^ s.card := by
  refine Finset.sum_bij (fun p _ => p.parts.toFinset) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Franklin.mem_DP]
    constructor
    · intro h0
      exact absurd (p.parts_pos (Multiset.mem_toFinset.mp h0)) (by simp)
    · rw [Finset.sum_eq_multiset_sum]
      simpa [Multiset.dedup_eq_self.mpr hp.2] using p.parts_sum
  · intro p hp q hq h
    rw [Finset.mem_filter] at hp hq
    apply Nat.Partition.ext
    have := congrArg Finset.val h
    simpa [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hp.2, Multiset.dedup_eq_self.mpr hq.2]
      using this
  · intro s hs
    rw [Franklin.mem_DP] at hs
    refine ⟨⟨s.val, ?_, ?_⟩, ?_, ?_⟩
    · intro i hi
      have : i ≠ 0 := by rintro rfl; exact hs.1 hi
      omega
    · rw [← hs.2, Finset.sum_eq_multiset_sum]; simp
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, s.nodup⟩
    · simp
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Multiset.toFinset_card_of_nodup hp.2]

/-- The generating function attached to `fsgn` is the series with coefficients
`pentagonalCoeff`; this is Franklin's theorem restated for power series. -/

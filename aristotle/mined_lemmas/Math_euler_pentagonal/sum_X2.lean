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

lemma sum_X2 (n : ℕ) :
    (∑ s ∈ X2 n, (-1 : ℤ) ^ s.card)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * n = k * (3 * k + 1) ∧ k ≠ 0),
          (-1 : ℤ) ^ k := by
  refine Finset.sum_nbij' (fun s => s.card) (fun k => Finset.Ico (k + 1) (2 * k + 1)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [X2, Finset.mem_filter, mem_DP] at hs
    obtain ⟨⟨h0, hsum⟩, hshape, hne⟩ := hs
    have hsum' : ∑ i ∈ Finset.Ico (s.card + 1) (2 * s.card + 1), i = n := by
      rw [← hshape]; exact hsum
    have hpent := sum_stair2 s.card
    rw [hsum'] at hpent
    have hk_le := le_of_pent2 hpent
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpent, hne⟩
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hcard : (Finset.Ico (k + 1) (2 * k + 1)).card = k := by rw [Nat.card_Ico]; omega
    simp only [X2, Finset.mem_filter]
    exact ⟨stair2_mem_DP hk.2.1, by rw [hcard], by rw [hcard]; exact hk.2.2⟩
  · intro s hs
    simp only [X2, Finset.mem_filter] at hs
    exact hs.2.1.symm
  · intro k hk
    simp only [Nat.card_Ico]
    omega
  · intro s _
    rfl


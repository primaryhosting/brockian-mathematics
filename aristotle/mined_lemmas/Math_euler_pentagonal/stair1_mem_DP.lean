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

lemma stair1_mem_DP {n k : ℕ} (hk : 2 * n = k * (3 * k - 1)) :
    Finset.Ico k (2 * k) ∈ DP n := by
  rw [mem_DP]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp
    · exact zero_notMem_Ico hk1
  · have := sum_stair1 k
    omega

/-- The staircases `{k+1, …, 2k}`. -/

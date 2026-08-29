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

lemma stair2_mem_DP {n k : ℕ} (hk : 2 * n = k * (3 * k + 1)) :
    Finset.Ico (k + 1) (2 * k + 1) ∈ DP n := by
  rw [mem_DP]
  refine ⟨zero_notMem_Ico (by omega), ?_⟩
  have := sum_stair2 k
  omega

/-- The exceptional sets of the first kind: `{k, …, 2k-1}` (including `∅` for `k = 0`). -/

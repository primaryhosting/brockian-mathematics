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

lemma run_exists (h0 : 0 ∉ s) : ∃ r, r ∈ {r | 1 ≤ r ∧ mx s - r ∉ s} := by
  refine ⟨max 1 (mx s), le_max_left _ _, ?_⟩
  have h : mx s - max 1 (mx s) = 0 := by omega
  rw [h]; exact h0


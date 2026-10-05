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

private lemma memL'_lt (h0 : 0 ∉ t) {x : ℕ}
    (hx : x ∈ t.filter (fun x => x ≤ mx t - run t)) : x < mx t - run t := by
  simp only [Finset.mem_filter] at hx
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact h
  · exact absurd (h ▸ hx.1) (run_notMem h0)


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

lemma op2_isA (h0 : 0 ∉ t) (hB : IsB t) : IsA (op2 t) := by
  refine ⟨op2_nonempty h0 hB, ?_, ?_⟩
  · rw [op2_mn h0 hB]; exact op2_run_ge h0 hB
  · rintro ⟨hcard, hrun⟩
    rw [op2_mn h0 hB] at hrun
    rw [op2_card h0 hB, hrun] at hcard
    have := run_le_card hB.1 h0
    omega


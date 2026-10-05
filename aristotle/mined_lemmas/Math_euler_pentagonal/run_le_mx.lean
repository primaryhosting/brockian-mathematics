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

lemma run_le_mx (hs : s.Nonempty) (h0 : 0 ∉ s) : run s ≤ mx s := by
  have h1 : 1 ≤ mx s := le_trans (mn_pos hs h0) (mn_le_mx hs)
  have : mx s ∈ {r | 1 ≤ r ∧ mx s - r ∉ s} := ⟨h1, by simpa using h0⟩
  exact Nat.sInf_le this


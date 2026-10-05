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

lemma IsB.two_run_lt_mx (h0 : 0 ∉ s) (hB : IsB s) : 2 * run s < mx s := by
  obtain ⟨hs, hlt, hne⟩ := hB
  have h1 := run_le_card hs h0
  have h2 := card_le_range hs
  have h3 := mn_le_mx hs
  have h4 := mn_pos hs h0
  have h5 := run_pos h0
  by_contra hc
  exact hne ⟨by omega, by omega⟩


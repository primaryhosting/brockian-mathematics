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

lemma op2_zero_notMem (h0 : 0 ∉ t) (hB : IsB t) : 0 ∉ op2 t := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  rw [op2_eq]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, not_or]
  exact ⟨by omega, fun h => h0 h.1, by rintro ⟨h, -⟩; omega⟩


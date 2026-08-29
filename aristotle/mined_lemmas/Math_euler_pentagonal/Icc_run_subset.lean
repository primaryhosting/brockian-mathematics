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

lemma Icc_run_subset (hs : s.Nonempty) : Finset.Icc (mx s - run s + 1) (mx s) ⊆ s := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · exact mx_mem hs
  · have hr : mx s - x < run s := by omega
    have h1 : 1 ≤ mx s - x := by omega
    have := run_minimal hr h1
    have hxx : mx s - (mx s - x) = x := by omega
    rwa [hxx] at this


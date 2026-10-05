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

private lemma disjB2 (h0 : 0 ∉ t) :
    Disjoint (t.filter (fun x => x ≤ mx t - run t)) (Finset.Icc (mx t - run t) (mx t - 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  have := memL'_lt h0 hx
  simp only [Finset.mem_Icc] at hx2
  omega


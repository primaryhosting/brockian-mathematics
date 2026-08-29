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

private lemma disjA1 :
    Disjoint ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s))
      (Finset.Icc (mx s - mn s + 1) (mx s)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  simp only [Finset.mem_filter, Finset.mem_erase] at hx
  simp only [Finset.mem_Icc] at hx2
  omega


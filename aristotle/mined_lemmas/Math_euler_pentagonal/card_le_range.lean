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

lemma card_le_range (hs : s.Nonempty) : s.card ≤ mx s - mn s + 1 := by
  have hsub : s ⊆ Finset.Icc (mn s) (mx s) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨mn_le hs hx, le_mx hx⟩
  have h := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h
  have := mn_le_mx hs
  omega

end Basic

section Moves

variable {s : Finset ℕ} {n : ℕ}

/-- `s` admits Franklin's first move: the smallest part is at most the length of the top run,
and `s` is not the exceptional staircase `{k, …, 2k-1}`. -/

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

lemma mx_Ico {a b : ℕ} (h : a < b) : mx (Finset.Ico a b) = b - 1 := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [id]; omega
  · exact Finset.le_sup (f := id) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)


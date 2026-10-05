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

lemma op1_mem (h0 : 0 ∉ s) (hA : IsA s) : mx s + 1 ∈ op1 s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hpos := mn_pos hA.1 h0
  rw [op1_eq]
  refine Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)


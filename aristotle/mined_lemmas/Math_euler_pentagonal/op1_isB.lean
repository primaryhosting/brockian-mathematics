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

lemma op1_isB (h0 : 0 ∉ s) (hA : IsA s) : IsB (op1 s) := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hrun := op1_run h0 hA
  have hmx := op1_mx h0 hA
  refine ⟨op1_nonempty h0 hA, ?_, ?_⟩
  · rw [hrun]
    exact op1_gt h0 hA (mn_mem (op1_nonempty h0 hA))
  · rintro ⟨hcard, hmn⟩
    rw [hrun] at hcard hmn
    -- `op1 s` has `mn s` elements, and contains the interval `Icc (mx s - mn s + 2) (mx s + 1)`
    have hsub : Finset.Icc (mx s - mn s + 2) (mx s + 1) ⊆ op1 s := by
      rw [op1_eq]; exact Finset.subset_union_right
    have hcard' : (Finset.Icc (mx s - mn s + 2) (mx s + 1)).card = mn s := card_IccA' h0 hA
    have heq : Finset.Icc (mx s - mn s + 2) (mx s + 1) = op1 s :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : mn (op1 s) ∈ Finset.Icc (mx s - mn s + 2) (mx s + 1) := by
      rw [heq]; exact mn_mem (op1_nonempty h0 hA)
    simp only [Finset.mem_Icc] at hmem
    omega


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

lemma op1_run (h0 : 0 ∉ s) (hA : IsA s) : run (op1 s) = mn s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hmx := op1_mx h0 hA
  have hpos := mn_pos hA.1 h0
  have hnot : mx (op1 s) - mn s ∉ op1 s := by
    rw [hmx, op1_eq]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, not_or]
    exact ⟨by rintro ⟨-, h⟩; omega, by rintro ⟨h, -⟩; omega⟩
  have hle : run (op1 s) ≤ mn s := Nat.sInf_le ⟨hpos, hnot⟩
  refine le_antisymm hle ?_
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ run (op1 s) := run_pos (op1_zero_notMem h0 hA)
  have hIcc : ∀ r : ℕ, 1 ≤ r → r < mn s → mx (op1 s) - r ∈ op1 s := by
    intro r hr1 hr2
    have hrw : mx (op1 s) - r = mx s + 1 - r := by rw [hmx]
    rw [hrw, op1_eq]
    exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  exact (run_notMem (op1_zero_notMem h0 hA)) (hIcc _ h1 hc)


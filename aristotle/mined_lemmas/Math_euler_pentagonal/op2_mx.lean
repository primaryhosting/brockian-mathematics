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

lemma op2_mx (h0 : 0 ∉ t) (hB : IsB t) : mx (op2 t) = mx t - 1 := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  have hmem : mx t - 1 ∈ op2 t := by
    rw [op2_eq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩))
  refine le_antisymm ?_ (le_mx hmem)
  rw [op2_eq]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hx
  simp only [id]
  rcases hx with rfl | ⟨hmem', hle⟩ | ⟨-, h⟩
  · omega
  · have := memL'_lt h0 (Finset.mem_filter.mpr ⟨hmem', hle⟩)
    omega
  · exact h


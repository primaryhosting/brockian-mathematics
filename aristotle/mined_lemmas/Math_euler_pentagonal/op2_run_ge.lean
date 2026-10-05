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

lemma op2_run_ge (h0 : 0 ∉ t) (hB : IsB t) : run t ≤ run (op2 t) := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  by_contra hc
  push_neg at hc
  have h3 : 1 ≤ run (op2 t) := run_pos (op2_zero_notMem h0 hB)
  have hmem : ∀ r : ℕ, 1 ≤ r → r < run t → mx (op2 t) - r ∈ op2 t := by
    intro r hr1 hr2
    have hrw : mx (op2 t) - r = mx t - 1 - r := by rw [op2_mx h0 hB]
    rw [hrw, op2_eq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  exact (run_notMem (op2_zero_notMem h0 hB)) (hmem _ h3 hc)


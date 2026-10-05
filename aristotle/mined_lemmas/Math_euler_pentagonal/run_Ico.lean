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

lemma run_Ico {a b : ℕ} (h : a < b) (ha : 1 ≤ a) : run (Finset.Ico a b) = b - a := by
  have h0 : (0 : ℕ) ∉ Finset.Ico a b := zero_notMem_Ico ha
  have hmx := mx_Ico h
  have hnot : mx (Finset.Ico a b) - (b - a) ∉ Finset.Ico a b := by
    rw [hmx]
    simp only [Finset.mem_Ico, not_and, not_lt]
    intro hc; omega
  have hle : run (Finset.Ico a b) ≤ b - a := Nat.sInf_le ⟨by omega, hnot⟩
  refine le_antisymm hle ?_
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ run (Finset.Ico a b) := run_pos h0
  have h2 : mx (Finset.Ico a b) - run (Finset.Ico a b) ∈ Finset.Ico a b := by
    rw [hmx]
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  exact run_notMem h0 h2

/-- A set whose top run exhausts it is an interval. -/

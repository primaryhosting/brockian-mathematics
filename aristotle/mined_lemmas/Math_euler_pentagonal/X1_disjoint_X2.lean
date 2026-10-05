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

lemma X1_disjoint_X2 (n : ℕ) : Disjoint (X1 n) (X2 n) := by
  rw [Finset.disjoint_left]
  intro s hs1 hs2
  simp only [X1, X2, Finset.mem_filter] at hs1 hs2
  obtain ⟨-, h1⟩ := hs1
  obtain ⟨-, h2, hne⟩ := hs2
  set k := s.card with hk
  have hk1 : 1 ≤ k := by omega
  have hmem : k ∈ s := by rw [h1]; exact Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
  rw [h2] at hmem
  simp only [Finset.mem_Ico] at hmem
  omega


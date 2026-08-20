/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of distinct vertices (indexed here by ordered pairs `i < j`). -/

lemma sum_g_double (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j = (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hrow : ∑ j ∈ Finset.range n, g n j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        simp only [g]
        rw [if_neg (by omega)]
      have hgnn : g n n = 0 := by simp [g]
      calc ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), g i j
          = ∑ i ∈ Finset.range (n + 1), ((∑ j ∈ Finset.range n, g i j) + g i n) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n, g i j)
              + ∑ i ∈ Finset.range (n + 1), g i n := Finset.sum_add_distrib
        _ = ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j) + ∑ j ∈ Finset.range n, g n j)
              + ((∑ i ∈ Finset.range n, g i n) + g n n) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (n + 1).choose 3 + (n + 1).choose 2 := by
            rw [ih, hrow, hgnn, sum_g_col]; omega
        _ = (n + 1 + 1).choose 3 := by
            have h := Nat.choose_succ_succ (n + 1) 2
            norm_num at h
            omega

/-- **The Wiener index of the path graph `P n` is `C(n+1, 3)`.** -/

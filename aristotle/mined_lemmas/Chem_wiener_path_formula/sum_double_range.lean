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

/-- The Wiener index of a graph on a linearly ordered finite vertex set: the sum of the
graph distances over all unordered pairs of distinct vertices. -/

lemma sum_double_range (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (if a < b then b - a else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hlast : ∑ b ∈ Finset.range (n + 1), (if n < b then b - n else 0) = 0 := by
        refine Finset.sum_eq_zero (fun b hb => ?_)
        simp only [Finset.mem_range] at hb
        have : ¬ n < b := by omega
        simp [this]
      have hrow : ∀ a ∈ Finset.range n,
          ∑ b ∈ Finset.range (n + 1), (if a < b then b - a else 0)
            = (∑ b ∈ Finset.range n, (if a < b then b - a else 0)) + (n - a) := by
        intro a ha
        simp only [Finset.mem_range] at ha
        rw [Finset.sum_range_succ]
        simp [ha]
      rw [Finset.sum_congr rfl hrow, hlast, Finset.sum_add_distrib, ih, sum_range_sub,
        add_zero]
      rw [Nat.choose_succ_succ' (n + 2) 2]
      omega

/-- **Wiener path formula**: the Wiener index of the path graph `P n` on `n` vertices equals
`(n+1).choose 3`. -/

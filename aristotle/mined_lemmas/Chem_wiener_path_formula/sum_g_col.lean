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

lemma sum_g_col (n : ℕ) : ∑ i ∈ Finset.range n, g i n = (n + 1).choose 2 := by
  have h1 : ∑ i ∈ Finset.range n, g i n = ∑ i ∈ Finset.range n, (i + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp only [g]
    rw [if_pos (by omega)]
    omega
  rw [h1, Finset.sum_add_distrib, sum_range_id_eq_choose, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, Nat.choose_succ_succ n 1]
  simp [Nat.add_comm]


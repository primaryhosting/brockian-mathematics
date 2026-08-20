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

lemma sum_range_id_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m 1]
      simp [Nat.add_comm]

/-- The auxiliary summand: `g i j = j - i` for `i < j`, and `0` otherwise. -/

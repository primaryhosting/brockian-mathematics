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

lemma natAbs_sub_le_walk_length {n : ℕ} :
    ∀ {i j : Fin n} (p : (pathGraph n).Walk i j), ((i : ℤ) - (j : ℤ)).natAbs ≤ p.length := by
  intro i j p
  induction p with
  | nil => simp
  | cons h p ih =>
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Upper bound for the distance in the path graph. -/

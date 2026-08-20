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

lemma nat_dist_le_walk_length {n : ℕ} {i j : Fin n} (w : (pathGraph n).Walk i j) :
    Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  induction w with
  | nil => simp [Nat.dist]
  | @cons a b c h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [Nat.dist] at *
      omega

/-- Upper bound on the distance in the path graph. -/

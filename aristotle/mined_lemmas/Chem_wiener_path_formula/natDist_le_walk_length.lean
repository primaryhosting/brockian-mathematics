import Mathlib
/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs. -/

lemma natDist_le_walk_length {n : ℕ} {i j : Fin n} (w : (pathGraph n).Walk i j) :
    Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons]
    simp only [Nat.dist] at *
    omega

/-- In the path graph there is a walk of length `k` from `i` to `i + k`. -/

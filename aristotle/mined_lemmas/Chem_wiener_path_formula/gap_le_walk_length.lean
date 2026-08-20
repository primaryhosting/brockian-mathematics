import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of vertices. -/

lemma gap_le_walk_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    (u : ℕ) - (v : ℕ) + ((v : ℕ) - (u : ℕ)) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [pathGraph_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Between two vertices of the path graph whose indices differ by `d` there is a walk of
length `d`. -/

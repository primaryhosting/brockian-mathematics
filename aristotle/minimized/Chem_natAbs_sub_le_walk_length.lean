/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph whose vertices carry a linear order:
the sum of the graph distances over all unordered pairs of distinct vertices
(each pair `{u, v}` counted once, via `u < v`). -/

lemma natAbs_sub_le_walk_length {n : ℕ} {u v : Fin n} (w : (pathGraph n).Walk u v) :
    ((u : ℤ) - (v : ℤ)).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons u x v h p ih =>
    rw [SimpleGraph.pathGraph_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Distance in the path graph is bounded above by the difference of the indices. -/

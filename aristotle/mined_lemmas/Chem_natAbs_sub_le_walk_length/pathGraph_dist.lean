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

lemma pathGraph_dist {n : ℕ} (i j : Fin n) (h : (i : ℕ) ≤ (j : ℕ)) :
    (pathGraph n).dist i j = (j : ℕ) - (i : ℕ) := by
  refine le_antisymm (pathGraph_dist_le_aux ((j : ℕ) - (i : ℕ)) i j (by omega)) ?_
  obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n i j).exists_walk_length_eq_dist
  have := natAbs_sub_le_walk_length p
  omega


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

lemma pathGraph_dist_le_aux {n : ℕ} (d : ℕ) : ∀ (i j : Fin n), (j : ℕ) = (i : ℕ) + d →
    (pathGraph n).dist i j ≤ d := by
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    simp [this]
  | succ d ih =>
    intro i j h
    have hj := j.isLt
    have hk : (i : ℕ) + d < n := by omega
    set k : Fin n := ⟨(i : ℕ) + d, hk⟩ with hkdef
    have h1 : (pathGraph n).dist i k ≤ d := ih i k rfl
    have h2 : (pathGraph n).dist k j = 1 := by
      rw [SimpleGraph.dist_eq_one_iff_adj, SimpleGraph.pathGraph_adj]
      left; simp [hkdef]; omega
    have h3 := (SimpleGraph.pathGraph_preconnected n i k).dist_triangle_left j
    omega

/-- The distance between two vertices of the path graph is the difference of their indices. -/

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

lemma exists_walk_pathGraph {n : ℕ} : ∀ (k : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + k →
    ∃ w : (pathGraph n).Walk i j, w.length = k := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
    intro i j h
    have hlt : (i : ℕ) + 1 < n := by omega
    let m : Fin n := ⟨(i : ℕ) + 1, hlt⟩
    have hadj : (pathGraph n).Adj i m := by
      rw [SimpleGraph.pathGraph_adj]; left; rfl
    obtain ⟨w, hw⟩ := ih m j (by simp only [m]; omega)
    exact ⟨SimpleGraph.Walk.cons hadj w, by simp [hw]⟩

/-- The distance in the path graph `P n` between `i` and `j` is `|i - j|`. -/

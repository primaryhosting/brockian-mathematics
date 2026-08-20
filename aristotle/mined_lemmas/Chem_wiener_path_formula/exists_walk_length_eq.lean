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

lemma exists_walk_length_eq {n : ℕ} :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + d →
      ∃ p : (pathGraph n).Walk i j, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
    intro i j h
    have hj : (j : ℕ) < n := j.isLt
    have hlt : (i : ℕ) + 1 < n := by omega
    let k : Fin n := ⟨(i : ℕ) + 1, hlt⟩
    have hadj : (pathGraph n).Adj i k := pathGraph_adj.2 (Or.inl rfl)
    obtain ⟨p, hp⟩ := ih k j (by simp only [k]; omega)
    exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩

/-- Key intermediate lemma: the distance between two vertices of the path graph is the
absolute difference of their indices. -/

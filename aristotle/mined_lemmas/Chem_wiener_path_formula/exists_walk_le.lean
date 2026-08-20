import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma exists_walk_le {n : ℕ} :
    ∀ (d : ℕ) (i j : Fin n), (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) = d →
      ∃ w : (pathGraph n).Walk i j, w.length = d := by
  intro d
  induction d with
  | zero =>
      intro i j hij h
      have : i = j := Fin.ext (by omega)
      subst this
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
      intro i j hij h
      have hjn : (j : ℕ) < n := j.isLt
      have hk : (i : ℕ) + 1 < n := by omega
      let k : Fin n := ⟨(i : ℕ) + 1, hk⟩
      have hadj : (pathGraph n).Adj i k := pathGraph_adj.2 (Or.inl rfl)
      obtain ⟨w, hw⟩ := ih k j (by simp [k]; omega) (by simp [k]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj w, by simp [hw]⟩

/-- Existence of a geodesic walk in the path graph. -/

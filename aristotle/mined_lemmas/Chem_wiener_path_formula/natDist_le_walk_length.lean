import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma natDist_le_walk_length {n : ℕ} :
    ∀ {i j : Fin n} (w : (pathGraph n).Walk i j), Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  intro i j w
  induction w with
  | nil => simp
  | cons h w ih =>
      rename_i i k j
      have h1 : Nat.dist (i : ℕ) (k : ℕ) = 1 := by
        rcases (pathGraph_adj).1 h with h' | h' <;> simp [Nat.dist] <;> omega
      calc Nat.dist (i : ℕ) (j : ℕ) ≤ Nat.dist (i : ℕ) (k : ℕ) + Nat.dist (k : ℕ) (j : ℕ) :=
            Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + w.length := by rw [h1]; exact Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons h w).length := by simp [Nat.add_comm]

/-- Existence of a geodesic walk in the path graph, in the ordered case. -/

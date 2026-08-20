import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma exists_walk_natDist {n : ℕ} (i j : Fin n) :
    ∃ w : (pathGraph n).Walk i j, w.length = Nat.dist (i : ℕ) (j : ℕ) := by
  rcases le_total (i : ℕ) (j : ℕ) with h | h
  · obtain ⟨w, hw⟩ := exists_walk_le (Nat.dist (i : ℕ) (j : ℕ)) i j h (by simp [Nat.dist]; omega)
    exact ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := exists_walk_le (Nat.dist (j : ℕ) (i : ℕ)) j i h (by simp [Nat.dist]; omega)
    exact ⟨w.reverse, by simpa [Nat.dist_comm] using hw⟩

/-- The distance between two vertices of the path graph `P_n` is the absolute
difference of their indices. -/

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

theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = (i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ)) := by
  apply le_antisymm
  · rcases le_total (i : ℕ) (j : ℕ) with h | h
    · obtain ⟨p, hp⟩ := exists_walk_length_eq ((j : ℕ) - (i : ℕ)) i j (by omega)
      have := SimpleGraph.dist_le p
      omega
    · obtain ⟨p, hp⟩ := exists_walk_length_eq ((i : ℕ) - (j : ℕ)) j i (by omega)
      have := SimpleGraph.dist_le p
      rw [SimpleGraph.dist_comm]
      omega
  · obtain ⟨p, hp⟩ := (pathGraph_preconnected n i j).exists_walk_length_eq_dist
    have := gap_le_walk_length p
    omega

/-! ### The combinatorial sum -/

/-- Gauss' sum, in the form needed below. -/

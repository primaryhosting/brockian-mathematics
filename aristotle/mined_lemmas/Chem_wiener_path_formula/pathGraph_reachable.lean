/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of distinct vertices (represented as ordered pairs `u < v`). -/

theorem pathGraph_reachable (n : ℕ) (u v : Fin n) : (pathGraph n).Reachable u v := by
  rcases le_total (u : ℕ) (v : ℕ) with h | h
  · obtain ⟨w, _⟩ := exists_walk_pathGraph n ((v : ℕ) - (u : ℕ)) u v (by omega)
    exact ⟨w⟩
  · obtain ⟨w, _⟩ := exists_walk_pathGraph n ((u : ℕ) - (v : ℕ)) v u (by omega)
    exact ⟨w.reverse⟩

/-- Any walk in the path graph has length at least the numeric distance of its endpoints. -/

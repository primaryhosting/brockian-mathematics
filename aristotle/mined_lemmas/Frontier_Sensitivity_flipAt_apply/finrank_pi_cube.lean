import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma finrank_pi_cube (n : ℕ) : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
  rw [Module.finrank_pi]
  simp

/-- Eigenspace of the signed adjacency matrix for the eigenvalue `c`. -/

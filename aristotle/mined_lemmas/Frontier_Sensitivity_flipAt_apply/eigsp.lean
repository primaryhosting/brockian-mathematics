import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

noncomputable def eigsp {n : ℕ} (c : ℝ) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (sgnAdj (n := n)) - c • LinearMap.id)


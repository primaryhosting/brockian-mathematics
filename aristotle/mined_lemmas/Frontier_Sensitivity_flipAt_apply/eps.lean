import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

def eps {n : ℕ} (u : Q n) (k : Fin n) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i < k), (if u i then (-1 : ℝ) else 1)

/-- Huang's signed adjacency matrix of the `n`-cube. -/

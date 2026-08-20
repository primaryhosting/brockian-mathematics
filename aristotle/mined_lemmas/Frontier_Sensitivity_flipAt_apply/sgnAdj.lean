import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

noncomputable def sgnAdj {n : ℕ} : Matrix (Q n) (Q n) ℝ :=
  Matrix.of fun u v => ∑ k : Fin n, if v = flipAt k u then eps u k else 0

/-! #### Basic properties of `flipAt` -/


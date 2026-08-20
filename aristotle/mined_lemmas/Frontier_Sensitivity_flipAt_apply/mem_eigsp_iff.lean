import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma mem_eigsp_iff {n : ℕ} (c : ℝ) (y : Q n → ℝ) :
    y ∈ eigsp (n := n) c ↔ sgnAdj *ᵥ y = c • y := by
  simp [eigsp, LinearMap.mem_ker, sub_eq_zero]

/-- `A² = n • 1` in the form of an identity for matrix-vector products. -/

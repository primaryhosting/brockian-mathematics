import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma sgnAdj_mulVec_sq {n : ℕ} (x : Q n → ℝ) :
    sgnAdj *ᵥ (sgnAdj *ᵥ x) = (n : ℝ) • x := by
  rw [Matrix.mulVec_mulVec, sgnAdj_mul_self]
  simp [Matrix.smul_mulVec]

/-- The two eigenspaces for `±√n` span everything. -/

import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma sgnAdj_eq_zero_of_forall {n : ℕ} {u v : Q n} (h : ∀ k : Fin n, v ≠ flipAt k u) :
    sgnAdj u v = 0 := by
  rw [sgnAdj]
  simp only [Matrix.of_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [h k]


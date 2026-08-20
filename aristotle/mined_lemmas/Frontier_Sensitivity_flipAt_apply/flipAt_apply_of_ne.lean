import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_apply_of_ne {n : ℕ} {k i : Fin n} (u : Q n) (h : i ≠ k) :
    flipAt k u i = u i := by
  simp [flipAt_apply, h]


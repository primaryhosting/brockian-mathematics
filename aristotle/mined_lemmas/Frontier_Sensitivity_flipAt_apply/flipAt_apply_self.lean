import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_apply_self {n : ℕ} (k : Fin n) (u : Q n) : flipAt k u k = !u k := by
  simp [flipAt_apply]


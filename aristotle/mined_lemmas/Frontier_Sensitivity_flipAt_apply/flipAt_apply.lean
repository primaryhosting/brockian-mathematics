import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_apply {n : ℕ} (k i : Fin n) (u : Q n) :
    flipAt k u i = if i = k then !u i else u i := by
  unfold flipAt
  by_cases h : i = k
  · subst h; simp
  · simp [h]


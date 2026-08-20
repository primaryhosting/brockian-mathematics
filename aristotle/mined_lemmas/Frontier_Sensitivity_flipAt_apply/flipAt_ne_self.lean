import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_ne_self {n : ℕ} (k : Fin n) (u : Q n) : flipAt k u ≠ u := by
  intro h
  have h2 := congrFun h k
  rw [flipAt_apply_self] at h2
  cases hu : u k <;> rw [hu] at h2 <;> simp at h2


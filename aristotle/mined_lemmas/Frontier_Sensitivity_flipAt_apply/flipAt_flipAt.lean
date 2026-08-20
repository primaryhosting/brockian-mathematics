import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

@[simp] lemma flipAt_flipAt {n : ℕ} (k : Fin n) (u : Q n) : flipAt k (flipAt k u) = u := by
  funext i
  simp only [flipAt_apply]
  split_ifs <;> simp_all


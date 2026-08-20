import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma abs_eps {n : ℕ} (u : Q n) (k : Fin n) : |eps u k| = 1 := by
  have h := eps_mul_self u k
  have h2 : |eps u k| * |eps u k| = 1 := by rw [← abs_mul, h]; simp
  nlinarith [abs_nonneg (eps u k)]

/-- Flipping the coordinate `k` does not change the sign associated with `l ≤ k`. -/

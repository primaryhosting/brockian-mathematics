import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma eps_mul_self {n : ℕ} (u : Q n) (k : Fin n) : eps u k * eps u k = 1 := by
  rw [eps, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one ?_
  intro i _
  by_cases h : u i <;> simp [h]


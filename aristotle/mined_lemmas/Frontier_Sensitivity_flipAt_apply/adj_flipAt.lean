import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma adj_flipAt {n : ℕ} (u : Q n) (k : Fin n) : adj (flipAt k u) u := by
  have h : (Finset.univ.filter (fun i => flipAt k u i ≠ u i)) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, flipAt_apply]
    by_cases h : i = k <;> simp [h]
  rw [adj, h, Finset.card_singleton]

/-- If the matrix entry is nonzero then the two vertices are adjacent. -/

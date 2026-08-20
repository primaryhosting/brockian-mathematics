import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma abs_sgnAdj_le_one {n : ℕ} (u v : Q n) : |sgnAdj u v| ≤ 1 := by
  by_cases h : ∃ k : Fin n, v = flipAt k u
  · obtain ⟨k, rfl⟩ := h
    rw [sgnAdj_apply_flipAt, abs_eps]
  · push_neg at h
    rw [sgnAdj_eq_zero_of_forall h]
    simp


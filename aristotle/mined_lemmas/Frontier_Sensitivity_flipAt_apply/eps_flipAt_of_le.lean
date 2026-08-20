import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma eps_flipAt_of_le {n : ℕ} (u : Q n) {k l : Fin n} (h : l ≤ k) :
    eps (flipAt k u) l = eps u l := by
  refine Finset.prod_congr rfl ?_
  intro i hi
  simp only [Finset.mem_filter] at hi
  have hik : i ≠ k := ne_of_lt (lt_of_lt_of_le hi.2 h)
  rw [flipAt_apply_of_ne _ hik]

/-- Flipping a coordinate `k` before `l` flips the sign associated with `l`. -/

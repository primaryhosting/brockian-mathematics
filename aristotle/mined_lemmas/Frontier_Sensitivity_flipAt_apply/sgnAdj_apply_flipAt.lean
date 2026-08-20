import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma sgnAdj_apply_flipAt {n : ℕ} (u : Q n) (k : Fin n) :
    sgnAdj u (flipAt k u) = eps u k := by
  rw [sgnAdj]
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    have h : flipAt k u ≠ flipAt l u := fun h => hl (flipAt_inj h.symm)
    simp [h]
  · intro h; exact absurd (Finset.mem_univ k) h


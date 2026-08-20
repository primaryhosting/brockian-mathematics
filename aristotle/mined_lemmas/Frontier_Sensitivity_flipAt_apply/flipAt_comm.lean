import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_comm {n : ℕ} (k l : Fin n) (u : Q n) :
    flipAt l (flipAt k u) = flipAt k (flipAt l u) := by
  funext i
  simp only [flipAt_apply]
  split_ifs <;> simp_all


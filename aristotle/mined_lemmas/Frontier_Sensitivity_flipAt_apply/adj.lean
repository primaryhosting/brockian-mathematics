import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

def adj {n : ℕ} (u v : Q n) : Prop :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

instance {n : ℕ} : DecidableRel (@adj n) := fun u v => by
  unfold adj; infer_instance

/-- Degree of `v` inside a vertex set `H`. -/

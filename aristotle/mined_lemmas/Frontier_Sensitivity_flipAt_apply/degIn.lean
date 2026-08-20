import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

def degIn {n : ℕ} (H : Finset (Q n)) (v : Q n) : ℕ :=
  (H.filter (fun u => adj u v)).card

/-! ### The signed adjacency matrix of the hypercube -/

/-- Flip the `k`-th coordinate of a vertex. -/

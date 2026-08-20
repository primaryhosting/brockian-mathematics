import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

def flipAt {n : ℕ} (k : Fin n) (u : Q n) : Q n := Function.update u k (!u k)

/-- The sign attached to flipping coordinate `k` of `u`: `(-1)` to the power of the
number of `1`-coordinates of `u` in positions before `k`. -/

import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

def emb (T : Finset (Fin n)) (hd : T.card = d) (j : Fin d) : Fin n :=
  (T.orderIsoOfFin hd j : Fin n)

/-- The extension of a vertex of the `d`-cube to a vertex of the `n`-cube, supported on `T`. -/

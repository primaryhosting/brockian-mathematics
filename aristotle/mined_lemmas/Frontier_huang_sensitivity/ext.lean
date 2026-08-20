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

def ext (T : Finset (Fin n)) (hd : T.card = d) (y : Q d) : Q n :=
  fun i => if h : i ∈ T then y ((T.orderIsoOfFin hd).symm ⟨i, h⟩) else false

variable (T : Finset (Fin n)) (hd : T.card = d)


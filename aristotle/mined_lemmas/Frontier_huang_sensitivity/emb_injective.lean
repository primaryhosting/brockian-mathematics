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

lemma emb_injective : Function.Injective (emb T hd) := by
  intro i j h
  have : (T.orderIsoOfFin hd) i = (T.orderIsoOfFin hd) j := Subtype.ext h
  exact (T.orderIsoOfFin hd).injective this


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

def sens (f : Q n → Bool) (x : Q n) : ℕ :=
  (univ.filter (fun i : Fin n => f (flipAt x i) ≠ f x)).card

/-- The sensitivity of a Boolean function. -/

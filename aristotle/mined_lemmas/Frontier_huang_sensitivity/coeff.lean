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

noncomputable def coeff (f : Q n → Bool) : Finset (Fin n) → ℝ :=
  (exists_multilinear_repr (fun x => if f x then (1 : ℝ) else 0)).choose


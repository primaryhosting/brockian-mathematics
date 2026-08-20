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

def mono (T : Finset (Fin n)) (x : Q n) : ℝ := ∏ i ∈ T, (if x i then (1 : ℝ) else 0)

/-- The vertex which is the indicator function of `T`. -/

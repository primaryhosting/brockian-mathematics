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

def Dlin (n : ℕ) : (Q n → ℝ) →ₗ[ℝ] (Q n → ℝ) where
  toFun v := fun x => sgn x * v x
  map_add' u v := by funext x; simp [mul_add]
  map_smul' c v := by funext x; simp [mul_left_comm]


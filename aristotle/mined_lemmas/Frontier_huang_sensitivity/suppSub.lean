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

noncomputable def suppSub (S : Finset (Q n)) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ (Subtype.val : {x : Q n // x ∉ S} → Q n))


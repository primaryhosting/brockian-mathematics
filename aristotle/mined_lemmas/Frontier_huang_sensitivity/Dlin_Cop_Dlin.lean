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

lemma Dlin_Cop_Dlin (v : Q n → ℝ) : Dlin n (Cop n (Dlin n v)) = Bop n v := by
  rw [Cop_apply, map_sub, map_smul, hL_Dlin, map_neg, Dlin_Dlin, Dlin_Dlin, Bop_apply]
  abel


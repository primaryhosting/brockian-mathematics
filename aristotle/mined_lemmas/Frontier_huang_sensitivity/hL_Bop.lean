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

lemma hL_Bop (v : Q n → ℝ) : hL n (Bop n v) = Real.sqrt n • Bop n v := by
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  rw [Bop_apply, map_add, map_smul, hL_hL, smul_add, smul_smul, hsq]
  abel


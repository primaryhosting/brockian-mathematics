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

lemma sgnp_mul_self (p : Fin n → Prop) [DecidablePred p] (x : Q n) :
    sgnp p x * sgnp p x = 1 := by
  simp [sgnp, ← pow_add, ← two_mul, pow_mul]


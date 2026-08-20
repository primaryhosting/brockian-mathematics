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

lemma hL_sgn (v : Q n → ℝ) (x : Q n) :
    hL n (fun y => sgn y * v y) x = - (sgn x * hL n v x) := by
  simp only [hL_apply, sgn_flipAt, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Matrix

section Huang

variable {n : ℕ}

/-- Multiplication by the global sign `sgn`. -/

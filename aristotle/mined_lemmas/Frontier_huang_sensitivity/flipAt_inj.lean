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

lemma flipAt_inj (x : Q n) {i j : Fin n} (h : flipAt x i = flipAt x j) : i = j := by
  by_contra hij
  have := congrFun h i
  rw [flipAt_apply_self, flipAt_apply_of_ne _ hij] at this
  simp at this

end Flip

section Sign

variable {n : ℕ}

/-- Number of coordinates `k` satisfying `p k` at which `x` is `true`. -/

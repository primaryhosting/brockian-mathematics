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

@[simp] lemma flipAt_flipAt (x : Q n) (i : Fin n) : flipAt (flipAt x i) i = x := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [flipAt_apply_of_ne _ h]


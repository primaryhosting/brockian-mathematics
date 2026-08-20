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

lemma hasDegLE_bdeg (f : Q n → Bool) : HasDegLE f (bdeg f) := by
  have h : bdeg f ∈ {d | HasDegLE f d} := Nat.sInf_mem ⟨n, hasDegLE_top f⟩
  exact h


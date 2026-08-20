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

lemma coeff_eq_zero_of_lt {f : Q n → Bool} {T : Finset (Fin n)} (hT : bdeg f < T.card) :
    coeff f T = 0 := by
  obtain ⟨p, hp0, hp⟩ := hasDegLE_bdeg f
  rw [← eq_coeff_of_repr hp]
  exact hp0 T hT

/-- Some coefficient of maximal degree is nonzero. -/

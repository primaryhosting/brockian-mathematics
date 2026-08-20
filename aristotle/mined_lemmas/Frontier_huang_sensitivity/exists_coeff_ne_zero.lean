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

lemma exists_coeff_ne_zero (f : Q n → Bool) (hd : 0 < bdeg f) :
    ∃ T : Finset (Fin n), T.card = bdeg f ∧ coeff f T ≠ 0 := by
  by_contra hc
  push_neg at hc
  have : HasDegLE f (bdeg f - 1) := by
    refine ⟨coeff f, ?_, coeff_spec f⟩
    intro T hT
    rcases lt_trichotomy T.card (bdeg f) with h | h | h
    · omega
    · exact hc T h
    · exact coeff_eq_zero_of_lt h
  have := bdeg_le this
  omega

end Coeff

section Restriction

variable {n d : ℕ}

/-- The `j`-th element of `T`, as a coordinate of the big cube. -/

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

lemma hasDegLE_top (f : Q n → Bool) : HasDegLE f n := by
  refine ⟨coeff f, ?_, coeff_spec f⟩
  intro T hT
  have := Finset.card_le_univ T
  rw [Fintype.card_fin] at this
  omega


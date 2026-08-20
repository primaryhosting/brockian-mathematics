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

lemma hasDegLE_mono {f : Q n → Bool} {a b : ℕ} (h : HasDegLE f a) (hab : a ≤ b) :
    HasDegLE f b := by
  obtain ⟨p, hp0, hp⟩ := h
  exact ⟨p, fun T hT => hp0 T (lt_of_le_of_lt hab hT), hp⟩


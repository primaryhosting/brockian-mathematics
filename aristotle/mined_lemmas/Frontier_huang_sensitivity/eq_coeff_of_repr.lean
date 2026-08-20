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

lemma eq_coeff_of_repr {f : Q n → Bool} {p : Finset (Fin n) → ℝ}
    (hp : ∀ x : Q n, (if f x then (1 : ℝ) else 0) = ∑ T : Finset (Fin n), p T * mono T x) :
    p = coeff f :=
  repr_unique (fun x => by rw [← hp x, coeff_spec f x])

/-- The degree of a Boolean function: the least `d` with a representing multilinear
polynomial of degree at most `d`. -/

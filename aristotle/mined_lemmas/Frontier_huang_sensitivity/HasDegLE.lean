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

def HasDegLE (f : Q n → Bool) (d : ℕ) : Prop :=
  ∃ p : Finset (Fin n) → ℝ, (∀ T : Finset (Fin n), d < T.card → p T = 0) ∧
    ∀ x : Q n, (if f x then (1 : ℝ) else 0) = ∑ T : Finset (Fin n), p T * mono T x

/-- The alternating sum `∑ₓ (-1)^{|x|} f(x)`; it is, up to sign, the coefficient of
`x₁ ⋯ xₙ` in the multilinear representation of `f`. -/

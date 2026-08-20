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

lemma sgn_eq_of_par (x : Q n) : sgn x = if par x then -1 else 1 := by
  by_cases h : par x = true
  · rw [if_pos h]
    exact (par_eq_true_iff x).1 h
  · rw [if_neg (by simpa using h)]
    rcases mul_self_eq_one_iff.1 (sgn_mul_self x) with h1 | h1
    · exact h1
    · exact absurd ((par_eq_true_iff x).2 h1) (by simpa using h)

/-- The alternating sum of a monomial of degree `< n` vanishes. -/

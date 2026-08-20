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

lemma mono_univ (x : Q n) : mono univ x = if x = (fun _ => true) then 1 else 0 := by
  unfold mono
  by_cases h : x = (fun _ => true)
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i = false := by
      by_contra hc
      push_neg at hc
      exact h (funext (fun i => by simpa using hc i))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The multilinear monomials are linearly independent. -/

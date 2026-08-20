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

lemma topSum_eq (hn : 1 ≤ n) (f : Q n → Bool) :
    topSum f = ((univ.filter (fun x => f x ≠ par x)).card : ℝ) - 2 ^ (n - 1) := by
  have hpt : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
      = (if f x ≠ par x then (1 : ℝ) else 0) - (if par x then (1 : ℝ) else 0) := by
    intro x
    rw [sgn_eq_of_par]
    by_cases hp : par x = true <;> by_cases hf : f x = true <;>
      simp [hp, hf]
  unfold topSum
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole, card_par hn]
  norm_num


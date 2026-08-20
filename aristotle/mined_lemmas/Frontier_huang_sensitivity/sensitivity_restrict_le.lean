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

lemma sensitivity_restrict_le (f : Q n → Bool) :
    sensitivity (restrict T hd f) ≤ sensitivity f := by
  unfold sensitivity
  refine Finset.sup_le (fun y _ => ?_)
  exact (sens_restrict_le T hd f y).trans
    (Finset.le_sup (f := sens f) (Finset.mem_univ (ext T hd y)))

/-- The alternating sum of the restriction picks out the top coefficient. -/

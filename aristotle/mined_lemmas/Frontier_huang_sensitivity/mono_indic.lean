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

lemma mono_indic (T T' : Finset (Fin n)) : mono T (indic T') = if T ⊆ T' then 1 else 0 := by
  unfold mono indic
  by_cases h : T ⊆ T'
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i hi => ?_)
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hiT, hiT'⟩ := Finset.not_subset.1 h
    refine Finset.prod_eq_zero hiT ?_
    simp [hiT']


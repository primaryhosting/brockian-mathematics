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

lemma mono_ext_of_not_subset {T' : Finset (Fin n)} (hT' : ¬ T' ⊆ T) (y : Q d) :
    mono T' (ext T hd y) = 0 := by
  obtain ⟨i, hiT', hiT⟩ := Finset.not_subset.1 hT'
  exact Finset.prod_eq_zero hiT' (by rw [ext_of_not_mem T hd _ hiT]; simp)

/-- The restriction of `f` to the subcube spanned by the coordinates in `T`. -/

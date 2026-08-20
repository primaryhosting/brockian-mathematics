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

lemma repr_unique {p q : Finset (Fin n) → ℝ}
    (h : ∀ x : Q n, ∑ T : Finset (Fin n), p T * mono T x
      = ∑ T : Finset (Fin n), q T * mono T x) : p = q := by
  funext T
  have hz : ∀ x : Q n, ∑ T : Finset (Fin n), (p T - q T) * mono T x = 0 := by
    intro x
    have := h x
    rw [Finset.sum_congr rfl (fun T _ => sub_mul (p T) (q T) (mono T x)),
      Finset.sum_sub_distrib, this, sub_self]
  have := mono_indep (fun T => p T - q T) hz T
  linarith [this]

/-- The coefficients of the multilinear representation of `f`. -/

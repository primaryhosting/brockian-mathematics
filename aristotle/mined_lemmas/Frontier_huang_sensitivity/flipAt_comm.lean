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

lemma flipAt_comm (x : Q n) (i j : Fin n) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext k
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne k j with rfl | hkj
    · rfl
    · simp [flipAt_apply_of_ne _ hkj]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [flipAt_apply_of_ne _ hki]
    · simp [flipAt_apply_of_ne _ hki, flipAt_apply_of_ne _ hkj]


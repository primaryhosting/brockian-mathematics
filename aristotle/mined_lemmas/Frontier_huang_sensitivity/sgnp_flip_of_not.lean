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

lemma sgnp_flip_of_not (p : Fin n → Prop) [DecidablePred p] (x : Q n) {j : Fin n}
    (hj : ¬ p j) : sgnp p (flipAt x j) = sgnp p x := by
  have : cnt p (flipAt x j) = cnt p x := by
    unfold cnt
    congr 1
    apply Finset.filter_congr
    intro k _
    rcases eq_or_ne k j with rfl | hk
    · simp [hj]
    · simp [flipAt_apply_of_ne _ hk]
  simp [sgnp, this]


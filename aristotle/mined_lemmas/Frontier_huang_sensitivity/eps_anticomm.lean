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

lemma eps_anticomm (x : Q n) {i j : Fin n} (hij : i ≠ j) :
    eps x i * eps (flipAt x i) j = - (eps x j * eps (flipAt x j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : eps (flipAt x i) j = eps x j := sgnp_flip_of_not _ _ (asymm h)
    have h2 : eps (flipAt x j) i = - eps x i := sgnp_flip_of_mem _ _ h
    rw [h1, h2]; ring
  · have h1 : eps (flipAt x i) j = - eps x j := sgnp_flip_of_mem _ _ h
    have h2 : eps (flipAt x j) i = eps x i := sgnp_flip_of_not _ _ (asymm h)
    rw [h1, h2]; ring


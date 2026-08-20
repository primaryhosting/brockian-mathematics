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

lemma sum_sgn_mono_univ : ∑ x : Q n, sgn x * mono univ x = sgn (fun _ : Fin n => true) := by
  rw [Finset.sum_congr rfl (fun x _ => by rw [mono_univ])]
  rw [Finset.sum_eq_single (fun _ => true : Q n)]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The number of odd-weight vertices of the `n`-cube is `2^(n-1)`. -/

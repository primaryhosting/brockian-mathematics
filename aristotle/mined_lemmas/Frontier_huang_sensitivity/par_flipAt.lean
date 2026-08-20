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

lemma par_flipAt (x : Q n) (i : Fin n) : par (flipAt x i) ≠ par x := by
  intro h
  have hs : sgn (flipAt x i) = - sgn x := sgn_flipAt x i
  have hcases : sgn x = 1 ∨ sgn x = -1 := mul_self_eq_one_iff.1 (sgn_mul_self x)
  rcases hcases with h1 | h1
  · have hp : par x = false := by
      by_contra hp
      have := (par_eq_true_iff x).1 (by simpa using hp)
      rw [h1] at this; norm_num at this
    have hp' : par (flipAt x i) = false := by rw [h, hp]
    have : sgn (flipAt x i) = 1 := by
      rcases mul_self_eq_one_iff.1 (sgn_mul_self (flipAt x i)) with h2 | h2
      · exact h2
      · exact absurd ((par_eq_true_iff (flipAt x i)).2 h2) (by simp [hp'])
    rw [hs, h1] at this; norm_num at this
  · have hp : par x = true := (par_eq_true_iff x).2 h1
    have hp' : par (flipAt x i) = true := by rw [h, hp]
    have : sgn (flipAt x i) = -1 := (par_eq_true_iff _).1 hp'
    rw [hs, h1] at this; norm_num at this

/-- **Huang's sensitivity theorem**, combinatorial form: if the set of points where a
Boolean function `f` differs from the parity function does not have exactly half of the
`2^n` points of the cube, then the sensitivity of `f` is at least `√n`. -/

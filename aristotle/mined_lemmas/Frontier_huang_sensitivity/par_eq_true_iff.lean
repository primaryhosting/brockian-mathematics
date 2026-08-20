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

lemma par_eq_true_iff (x : Q n) : par x = true ↔ sgn x = -1 := by
  have h : cnt (fun _ : Fin n => True) x = (univ.filter (fun j => x j = true)).card := by
    unfold cnt; congr 1; apply Finset.filter_congr; intro k _; simp
  constructor
  · intro hp
    have hodd : Odd (univ.filter (fun j => x j = true)).card := by simpa [par] using hp
    simp [sgn, sgnp, h, Odd.neg_one_pow hodd]
  · intro hs
    by_contra hp
    have hev : ¬ Odd (univ.filter (fun j => x j = true)).card := by simpa [par] using hp
    rw [Nat.not_odd_iff_even] at hev
    rw [sgn, sgnp, h, Even.neg_one_pow hev] at hs
    norm_num at hs


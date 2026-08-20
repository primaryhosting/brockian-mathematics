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

theorem bdeg_and_two : bdeg (fun x : Q 2 => x 0 && x 1) = 2 := by
  have hle : bdeg (fun x : Q 2 => x 0 && x 1) ≤ 2 := bdeg_le (hasDegLE_top _)
  have hnot : ¬ HasDegLE (fun x : Q 2 => x 0 && x 1) 1 := by
    intro hdeg
    have h := topSum_eq_zero_of_hasDegLE (n := 2) (by norm_num) hdeg
    rw [topSum_eq (by norm_num)] at h
    have hcard : (univ.filter (fun x : Q 2 => (x 0 && x 1) ≠ par x)).card = 3 := by decide
    rw [hcard] at h
    norm_num at h
  have hgt : ¬ (bdeg (fun x : Q 2 => x 0 && x 1) ≤ 1) :=
    fun hb => hnot (hasDegLE_mono (hasDegLE_bdeg _) hb)
  omega

end Main

end Frontier

import RequestProject.Huang

open Finset

namespace Frontier

/-! # Degree of a Boolean function and Huang's theorem in the full-degree case

Every Boolean function `f : {0,1}^n → {0,1}` is represented by a unique multilinear
polynomial with real coefficients.  We define `Frontier.HasDegLE f d` to mean that `f` is
represented by a multilinear polynomial all of whose monomials have degree at most `d`, so
that "`f` has degree `n`" is `¬ HasDegLE f (n-1)`.

The main result `Frontier.huang_sensitivity` states that a Boolean function of full degree
`n` has sensitivity at least `√n`.
-/

section Multilinear

variable {n : ℕ}

/-- The multilinear monomial `∏ i ∈ T, x i`, evaluated at a hypercube vertex. -/

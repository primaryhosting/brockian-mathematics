import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma bvol_HS {n : E3} (hn : n ≠ 0) : bvol (HS n) = 2 * π / 3 := by
  have h := bvol_split Set.univ MeasurableSet.univ hn
  rw [bvol_univ, Set.univ_inter, Set.univ_inter, ← neg_HS, bvol_neg] at h
  linarith


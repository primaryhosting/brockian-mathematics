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

lemma bvol_eq_zero_of_null {A : Set E3} (h : volume A = 0) : bvol A = 0 := by
  rw [bvol, measure_mono_null Set.inter_subset_right h, ENNReal.toReal_zero]

/-- Splitting off a null intersection. -/

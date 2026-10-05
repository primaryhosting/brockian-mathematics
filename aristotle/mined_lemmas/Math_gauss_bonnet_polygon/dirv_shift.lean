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

lemma dirv_shift (e f : E3) (s φ : ℝ) :
    dirv (dirv e f s) (dirv e f (s + π / 2)) φ = dirv e f (s + φ) := by
  simp only [dirv, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module


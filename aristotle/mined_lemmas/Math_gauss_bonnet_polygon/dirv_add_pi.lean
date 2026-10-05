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

lemma dirv_add_pi (e f : E3) (φ : ℝ) : dirv e f (φ + π) = -dirv e f φ := by
  simp only [dirv, Real.cos_add_pi, Real.sin_add_pi]
  module

/-! ### The standard wedge function -/

/-- The first standard basis vector of `E3`. -/

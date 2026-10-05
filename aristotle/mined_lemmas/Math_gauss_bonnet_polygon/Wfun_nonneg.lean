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

lemma Wfun_nonneg (θ : ℝ) : 0 ≤ Wfun θ := bvol_nonneg _

/-- The wedge volume only depends on the two angles, not on the orthonormal frame. -/

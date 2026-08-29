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

lemma bvol_univ : bvol Set.univ = 4 / 3 * Real.pi := by
  rw [bvol, Set.inter_univ, volume_closedBall_one,
    ENNReal.toReal_ofReal (by positivity)]

/-- Splitting the ball along a hyperplane. -/

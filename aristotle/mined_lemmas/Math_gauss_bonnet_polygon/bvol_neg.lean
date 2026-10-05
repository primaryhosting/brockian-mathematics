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

lemma bvol_neg (S : Set E3) : bvol (-S) = bvol S := by
  have hb : closedBall (0 : E3) 1 ∩ (-S) = -(closedBall (0 : E3) 1 ∩ S) := by
    ext x
    simp
  rw [bvol, bvol, hb, Measure.measure_neg]

/-- Volume is invariant under linear isometries. -/

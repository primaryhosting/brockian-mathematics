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

lemma volume_ball_inter_ne_top (S : Set E3) :
    volume (closedBall (0 : E3) 1 ∩ S) ≠ ⊤ :=
  ((measure_mono Set.inter_subset_left).trans_lt
    (isCompact_closedBall _ _).measure_lt_top).ne


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

lemma bvol_mono {A B : Set E3} (h : A ⊆ B) : bvol A ≤ bvol B :=
  ENNReal.toReal_le_toReal (volume_ball_inter_ne_top A) (volume_ball_inter_ne_top B) |>.2
    (measure_mono (Set.inter_subset_inter_right _ h))


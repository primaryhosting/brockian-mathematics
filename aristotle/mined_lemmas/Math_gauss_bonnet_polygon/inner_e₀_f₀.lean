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

lemma inner_e₀_f₀ : ⟪e₀, f₀⟫ = 0 := by
  simp [e₀, f₀, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- `Wfun θ` is the volume of the wedge of the unit ball of dihedral angle `θ`. -/

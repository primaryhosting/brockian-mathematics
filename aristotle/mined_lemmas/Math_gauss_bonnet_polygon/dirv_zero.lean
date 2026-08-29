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

lemma dirv_zero (e f : E3) : dirv e f 0 = e := by simp [dirv]

/-- The volume of the wedge cut out by two half-spaces whose inner normals make an angle `ψ`. -/

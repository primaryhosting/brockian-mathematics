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

def dirv (e f : E3) (φ : ℝ) : E3 := Real.cos φ • e + Real.sin φ • f

/-- The volume of the part of the unit ball lying in the two half-spaces with inner normals
`u` and `v`. -/

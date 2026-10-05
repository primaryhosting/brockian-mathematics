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

lemma dirv_ne_zero (φ : ℝ) : dirv e f φ ≠ 0 := by
  intro h
  have := norm_dirv he hf hef φ
  rw [h] at this
  simp at this

end Orthonormal

/-- The rotated pair generates the same rotating family. -/

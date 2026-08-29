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

lemma inner_dirv_shift_pair {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (s : ℝ) :
    ⟪dirv e f s, dirv e f (s + π / 2)⟫ = 0 := by
  rw [inner_dirv_dirv he hf hef]
  simp [Real.cos_pi_div_two]

/-- The three-term positive combination identity for coplanar unit vectors. -/

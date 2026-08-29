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

lemma norm_dirv (φ : ℝ) : ‖dirv e f φ‖ = 1 := by
  have h := inner_dirv_dirv he hf hef φ φ
  rw [real_inner_self_eq_norm_sq] at h
  simp only [sub_self, Real.cos_zero] at h
  nlinarith [norm_nonneg (dirv e f φ)]


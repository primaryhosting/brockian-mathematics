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

lemma inner_dirv_dirv (α β : ℝ) : ⟪dirv e f α, dirv e f β⟫ = Real.cos (α - β) := by
  have hfe : ⟪f, e⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hef
  have hee : ⟪e, e⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hff : ⟪f, f⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hf]; norm_num
  simp only [dirv, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hef, hfe, hee, hff, Real.cos_sub]
  ring


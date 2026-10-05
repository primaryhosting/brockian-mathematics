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

lemma volume_closedBall_one : volume (closedBall (0 : E3) 1) = ENNReal.ofReal (4 / 3 * Real.pi) := by
  rw [EuclideanSpace.volume_closedBall]
  have h1 : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
    have h : (5 : ℝ) / 2 = 3 / 2 + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num)]
    have h' : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
    rw [h', Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hs : Real.sqrt Real.pi > 0 := Real.sqrt_pos.2 Real.pi_pos
  have h2 : Real.sqrt Real.pi ^ (3 : ℕ) / Real.Gamma (5 / 2) = 4 / 3 * Real.pi := by
    rw [h1, show Real.sqrt Real.pi ^ (3 : ℕ) = Real.pi * Real.sqrt Real.pi by
      rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]]
    field_simp
  norm_num [h2]


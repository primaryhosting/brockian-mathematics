import Mathlib
namespace MS.Foundations


private theorem expTail_pos (n : ℕ) : 0 < (n ! : ℝ) * (Real.exp 1 - expPartial n) := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (n + 2)
  rw [Finset.sum_range_succ] at h
  have hfn : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hp : (0 : ℝ) < 1 ^ (n + 1) / (((n + 1)! : ℕ) : ℝ) := by positivity
  have hgt : (0 : ℝ) < Real.exp 1 - expPartial n := by
    simp only [expPartial]; linarith
  exact mul_pos hfn hgt

/-- `n! * (e - S_{n+1}) < 1` for `n ≥ 1`, from the standard tail bound on the exponential series. -/

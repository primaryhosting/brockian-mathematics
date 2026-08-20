import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma tail_key (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (A : ℤ)
    (hA : (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) :
    |(n ! : ℝ) * Real.exp x - A
        - (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
            + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))))|
      ≤ ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3)) := by
  have h1 := partial_sum_mul x n A hA
  have h2 := exp_err x hx n
  have h3 := fact_ratio_err n
  -- n! * exp x - A - main_terms = n! * (exp x - partial sum)
  have heq : (n ! : ℝ) * Real.exp x - A - (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
      + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) =
      (n ! : ℝ) * (Real.exp x - ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)) := by
    linarith [h1]
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n !)]
  apply le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h3.le

/-- `n ! * e` is a positive amount (at most `2/(n+1)`) above an integer. -/

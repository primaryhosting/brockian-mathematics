import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma partial_sum_mul (x : ℝ) (n : ℕ) (A : ℤ)
    (hA : (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) :
    (n ! : ℝ) * ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)
      = A + (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
          + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) := by
  rw [sum_split3]
  rw [hA]
  have h1 : (n ! : ℝ) * (x ^ (n + 1) / ((n + 1)! : ℝ)) = x ^ (n + 1) * (1 / ((n : ℝ) + 1)) := by
    rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, fact_ratio_one]
  have h2 : (n ! : ℝ) * (x ^ (n + 2) / ((n + 2)! : ℝ)) = x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, fact_ratio_two]
  rw [mul_add, mul_add, h1, h2]
  ring

/-- The key approximation: if `A = n ! * (partial sum up to `n`)`, then `n ! * exp x` differs
from `A` by the two next terms of the series, up to a small error. -/

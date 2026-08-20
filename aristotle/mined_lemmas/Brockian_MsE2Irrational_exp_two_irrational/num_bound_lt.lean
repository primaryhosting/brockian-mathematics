import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma num_bound_lt (n : ℕ) :
    ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3))
      < 1 / ((n : ℝ) + 1) + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  field_simp
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1), sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]

/-- Truncation error of the exponential series after `n + 3` terms, for `|x| ≤ 1`. -/

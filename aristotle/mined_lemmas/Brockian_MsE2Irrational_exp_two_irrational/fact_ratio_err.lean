import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma fact_ratio_err (n : ℕ) :
    (n ! : ℝ) * ((n + 4) / (((n + 3)! : ℝ) * (n + 3)))
      = (n + 4) / ((n + 1) * (n + 2) * (n + 3) * (n + 3)) := by
  have h1 : (n + 3)! = (n + 3) * (n + 2) * (n + 1) * n ! := by
    simp [Nat.factorial_succ, mul_assoc]
  simp [h1]
  field_simp

/-- `n ! * (partial sum of the series for `e`)` is an integer. -/

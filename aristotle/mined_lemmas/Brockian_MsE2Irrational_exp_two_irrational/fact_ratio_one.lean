import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma fact_ratio_one (n : ℕ) : (n ! : ℝ) / ((n + 1)! : ℝ) = 1 / (n + 1) := by
  rw [factorial_succ]
  field_simp
  push_cast
  ring


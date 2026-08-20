import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma fact_ratio_two (n : ℕ) :
    (n ! : ℝ) / ((n + 2)! : ℝ) = 1 / ((n + 1) * (n + 2)) := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  field_simp
  norm_cast
  ring


/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`.
By convention `rad 0 = rad 1 = 1`. -/

theorem mem_abcExceptional_one_eight_nine : (1, 8, 9) ∈ abcExceptional (1 / 5) := by
  refine ⟨one_pos, by norm_num, Nat.coprime_one_left _, by norm_num, ?_⟩
  have hrad : rad (1 * 8 * 9) = 6 := by norm_num [rad_72]
  rw [hrad]
  have h6 : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
  rw [h6, show (1 : ℝ) + 1 / 5 = 6 / 5 by norm_num]
  have h : ((6 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℕ) = 6 ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast ((6 : ℝ) ^ ((6 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 5 (by norm_num) ?_
  rw [h]
  norm_num

/-- If the exceptional set for `ε` has bounded `c`, then it is finite. -/

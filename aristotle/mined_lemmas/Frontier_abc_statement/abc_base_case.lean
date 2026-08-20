/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

theorem abc_base_case : ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hrad : rad (1 * 8 * 9) = 6 := by
    have h : (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [rad, h, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide
  simp only [hrad]
  norm_num

/-- The triples `1 + (9 ^ n - 1) = 9 ^ n` (for `n ≥ 1`) are all exceptional at `ε = 0`:
since `8 ∣ 9 ^ n - 1`, one has `rad (a * b * c) ≤ 3 * (9 ^ n - 1) / 4 < 9 ^ n = c`. -/

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

theorem rad_72 : rad 72 = 6 := by
  have hpf : (72 : ℕ).primeFactors = {2, 3} := by
    have h : (72 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    rfl
  simp [rad, hpf]

/-- The exceptional set is nonempty for small `ε`: the classical triple `1 + 8 = 9`
satisfies `rad (1 * 8 * 9) ^ (1 + 1/5) = 6 ^ (6/5) < 9`. -/

/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ArithmeticFunction.sigma

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when
each is the sum of the *nontrivial* proper divisors of the other, equivalently
`σ m = σ n = m + n + 1`. -/

lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, sum_range_two_pow]

/-- `σ p = p + 1` for a prime `p`. -/

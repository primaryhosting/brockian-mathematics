/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two distinct positive naturals `m`, `n` are a *betrothed* (quasi-amicable) pair
when each is the sum of the *nontrivial* proper divisors of the other, equivalently
`σ m = σ n = m + n + 1`. -/

theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]

/-- `σ (2 ^ k * p) = (2 ^ (k+1) - 1) * (p + 1)` for an odd prime `p`. -/

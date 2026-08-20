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

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, Nat.add_comm] using h

/-- **Key intermediate lemma.**  For an odd prime `p`, the divisor sum of `2 ^ k * p`
factors as `(2 ^ (k+1) - 1) * (p + 1)`. -/

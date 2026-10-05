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

def SigmaCriterion (k p m n : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ n = 2 ^ k * p ∧ m = 2 ^ k * p + 2 ^ (k + 1) - p - 2 ∧
    σ 1 m = (2 ^ (k + 1) - 1) * (p + 1)


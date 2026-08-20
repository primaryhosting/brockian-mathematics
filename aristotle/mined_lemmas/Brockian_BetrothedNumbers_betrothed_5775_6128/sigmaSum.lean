import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The sum of all (positive) divisors of `n`, i.e. `σ₁ n`. -/

def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
each of whose divisor sums equals `m + n + 1`, i.e. the sum of the *proper* divisors of each
(excluding `1` and the number itself) equals the other number. -/

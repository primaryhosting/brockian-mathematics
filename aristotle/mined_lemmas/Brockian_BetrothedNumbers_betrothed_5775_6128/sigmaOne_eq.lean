import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`.  It agrees with Mathlib's
`ArithmeticFunction.sigma 1` (see `sigmaOne_eq`). -/

lemma sigmaOne_eq (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigmaOne]

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers such that the sum of the divisors of each, excluding the number itself and `1`,
equals the other one.  Equivalently `σ(m) = σ(n) = m + n + 1`. -/

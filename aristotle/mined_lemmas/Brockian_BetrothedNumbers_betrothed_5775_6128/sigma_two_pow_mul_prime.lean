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

theorem sigma_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_comm]
    exact (Nat.coprime_two_right_iff_odd).mpr hodd
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_two_pow,
    sigma_prime hp]

/-- Any parameters satisfying the `σ`-criterion produce a betrothed pair. -/

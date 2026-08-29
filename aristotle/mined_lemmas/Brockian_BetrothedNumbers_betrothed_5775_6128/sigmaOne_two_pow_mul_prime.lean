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

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem sigmaOne_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaOne (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  rw [sigmaOne_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ← sigmaOne_eq_sigma, ← sigmaOne_eq_sigma, sigmaOne_two_pow, sigmaOne_prime hp]

/-- If `m = 2 ^ k * p` with `p` an odd prime, and `n` is the number determined by the
criterion `n = σ₁(m) - m - 1` (equivalently `m + n + 1 = (2 ^ (k+1) - 1) * (p + 1)`),
and `n` has the same divisor sum, then `(n, m)` is a betrothed pair. -/

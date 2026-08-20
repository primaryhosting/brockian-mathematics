/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
whose sums of divisors both equal `n + m + 1`. -/

theorem sigma_one_mul_of_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (h : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_primes hq hr).mpr h)]
  rw [sigma_one_prime hq, sigma_one_prime hr]

/-- The sum of divisors of `2 ^ k * p` for `p` an odd prime. -/

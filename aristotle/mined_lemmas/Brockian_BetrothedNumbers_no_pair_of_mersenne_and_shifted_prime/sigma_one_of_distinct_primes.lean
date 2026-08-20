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

/-- Two positive natural numbers `m ≠ n` are a *betrothed* (quasi-amicable) pair when the sum of
the divisors of each of them equals `m + n + 1`, i.e. each is the sum of the *proper* divisors
of the other, excluding `1`. -/

lemma sigma_one_of_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_of_prime hq, sigma_one_of_prime hr]

/-- `σ₁` of `2 ^ k * p` for an odd prime `p`. -/

/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-- Two natural numbers `m` and `n` form a *betrothed* (quasi-amicable) pair when the sum of
divisors of each of them equals `m + n + 1`. -/

theorem sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_prime hp, sigma_one_prime hq]

/-- The sum of divisors of `2 ^ k * p` for an odd prime `p`. -/

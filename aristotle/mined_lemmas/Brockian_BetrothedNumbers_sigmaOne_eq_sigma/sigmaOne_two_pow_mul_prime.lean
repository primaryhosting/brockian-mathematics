import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

theorem sigmaOne_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaOne (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_primes Nat.prime_two hp]
    exact fun h => hp2 h.symm
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1) |>.map_mul_of_coprime hcop
  rw [sigmaOne_eq_sigma, hmul, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    sum_range_two_pow]
  congr 1
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- The `σ`-criterion generating a betrothed pair whose even member is `2 ^ k * p`
for an odd prime `p`: if `m` is a positive number distinct from `2 ^ k * p` with
`σ₁ m = (2 ^ (k+1) - 1) * (p + 1)` and `m + 2 ^ k * p + 1` equals that same value,
then `(m, 2 ^ k * p)` is a betrothed pair. -/

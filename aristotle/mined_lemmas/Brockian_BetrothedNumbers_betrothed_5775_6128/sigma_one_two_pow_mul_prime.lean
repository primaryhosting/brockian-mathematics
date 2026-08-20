/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when the
sum of the proper divisors of each, excluding `1`, gives the other; equivalently
`σ 1 m = σ 1 n = m + n + 1`. -/

theorem sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_apply_prime_pow Nat.prime_two, ← pow_one p,
    sigma_one_apply_prime_pow hp]
  simp only [Nat.geomSum_eq (le_refl 2), Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]
  norm_num [Nat.add_comm 1 p]

/-- The pair `(5775, 6128)` arises from the `k = 4`, `p = 383` sigma criterion:
`383` is prime, `6128 = 2 ^ 4 * 383`, and the common value
`σ 1 6128 = (2 ^ 5 - 1) * (383 + 1) = 11904` equals `5775 + 6128 + 1 = σ 1 5775`. -/

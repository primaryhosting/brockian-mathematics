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

set_option maxRecDepth 100000

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem sigma1_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigma1 (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_primes Nat.prime_two hp]
    exact fun h => hp2 h.symm
  have h1 : sigma1 (2 ^ k * p) = (∑ i ∈ Finset.range (k + 1), 2 ^ i) * (p + 1) := by
    unfold sigma1
    have hpd : ∑ d ∈ p.divisors, d = p + 1 := by
      rw [hp.divisors, Finset.sum_pair hp.ne_one.symm]; omega
    rw [hcop.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two, hpd]
  rw [h1, ← sum_range_two_pow (k + 1)]
  ring

/-- **The sigma criterion.** If `p` is an odd prime and `a` is a positive integer, distinct
from `b = 2 ^ k * p`, such that both `σ₁ a` and `a + b + 1` equal
`σ₁ b = (2 ^ (k+1) - 1) * (p + 1)`, then `(a, 2 ^ k * p)` is a betrothed pair.
(The equalities are written in the subtraction-free form `x + (p + 1) = 2 ^ (k+1) * (p + 1)`.) -/

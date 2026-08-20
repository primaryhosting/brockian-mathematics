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

lemma sigmaSum_two_pow_mul_prime (k p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaSum (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [sigmaSum_eq_sigma_one, isMultiplicative_sigma.map_mul_of_coprime hcop,
    ← sigmaSum_eq_sigma_one, ← sigmaSum_eq_sigma_one, sigmaSum_two_pow]
  unfold sigmaSum
  rw [hp.sum_divisors]

/-- **Key intermediate lemma (the `σ` criterion).**  If `p` is an odd prime, `m` is a positive
integer different from `2 ^ k * p`, and both `σ₁ m` and `m + 2 ^ k * p + 1` equal
`(2 ^ (k + 1) - 1) * (p + 1) = σ₁ (2 ^ k * p)`, then `(m, 2 ^ k * p)` is a betrothed pair. -/

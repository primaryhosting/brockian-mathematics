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
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-- Two distinct positive naturals `m` and `n` form a *betrothed* (quasi-amicable) pair when
each one's sum of divisors equals `m + n + 1`, i.e. the sum of the proper divisors of each
(excluding `1` and the number itself) equals the other number. -/

lemma sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.gcd (2 ^ k) p = 1 := by
    have h2p : (2 : ℕ) ≠ p := by
      rintro rfl
      simp [Nat.odd_iff] at hodd
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 h2p)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow, sigma_one_prime hp]

/-- **Unique partner.** If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime),
then `m = (2 ^ k - 1) * (p + 2)`. -/

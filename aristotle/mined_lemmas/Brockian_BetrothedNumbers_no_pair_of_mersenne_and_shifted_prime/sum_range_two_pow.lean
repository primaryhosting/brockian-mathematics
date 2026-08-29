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

lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range (n + 1), 2 ^ i = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have : (2 : ℕ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by ring
      omega

/-- `σ₁` of a power of two. -/

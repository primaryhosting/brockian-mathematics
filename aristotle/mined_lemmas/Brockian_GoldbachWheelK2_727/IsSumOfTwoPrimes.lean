import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 8000

namespace Brockian

/-- `IsSumOfTwoPrimes n` states that `n` is a sum of two (not necessarily distinct) primes. -/

def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- **Goldbach wheel, K = 2, modulus 727.**
Every even number `n` with `4 ≤ n ≤ 727` is a sum of two primes.
The proof splits on the (finitely many) admissible values of `n` and exhibits an
explicit pair of primes in each branch. -/

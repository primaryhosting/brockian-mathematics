import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  Nat.nth_lt_nth Nat.infinite_setOf_prime |>.2 (Nat.lt_succ_self n)


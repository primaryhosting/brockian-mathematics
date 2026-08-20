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

lemma nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n


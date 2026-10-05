/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter

namespace Frontier

/-- The `n`-th prime number (`primeSeq 0 = 2`). -/

theorem setOf_prime_infinite : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOf_prime

/-- **Bounded prime gaps** (the "small gaps between primes" statement): some bound `B`
is attained by infinitely many prime gaps. -/

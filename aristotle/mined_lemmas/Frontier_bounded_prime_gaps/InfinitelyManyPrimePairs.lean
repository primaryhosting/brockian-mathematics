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

def InfinitelyManyPrimePairs : Prop :=
  ∃ d : ℕ, 0 < d ∧ {p : ℕ | p.Prime ∧ (p + d).Prime}.Infinite

section Reduction

/-- If `q` is a prime larger than the `n`-th prime, then the `(n+1)`-st prime is at most `q`. -/

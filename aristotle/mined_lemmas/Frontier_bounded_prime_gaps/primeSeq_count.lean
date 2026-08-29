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

theorem primeSeq_count {q : ℕ} (hq : q.Prime) : primeSeq (Nat.count Nat.Prime q) = q :=
  Nat.nth_count hq

/-- If `p` and `p + d` are both prime, then the prime gap at index `Nat.count Nat.Prime p`
is at most `d`. -/

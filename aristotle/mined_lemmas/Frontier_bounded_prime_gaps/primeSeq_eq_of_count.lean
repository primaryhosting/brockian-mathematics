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

theorem primeSeq_eq_of_count {n q : ℕ} (hq : q.Prime) (h : Nat.count Nat.Prime q = n) :
    primeSeq n = q := by
  subst h; exact Nat.nth_count hq


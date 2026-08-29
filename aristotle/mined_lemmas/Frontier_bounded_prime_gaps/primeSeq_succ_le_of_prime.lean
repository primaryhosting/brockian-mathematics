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

theorem primeSeq_succ_le_of_prime {n q : ℕ} (hq : q.Prime) (h : primeSeq n < q) :
    primeSeq (n + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.le_nth_of_lt_nth_succ hcon hq) (not_le.mpr h)

/-- Every prime is the `n`-th prime for `n = π(q) - 1`, i.e. `n = Nat.count Nat.Prime q`. -/

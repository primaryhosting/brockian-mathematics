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

theorem primeGap_le_of_prime_pair {p d : ℕ} (hp : p.Prime) (hpd : (p + d).Prime) (hd : 0 < d) :
    primeGap (Nat.count Nat.Prime p) ≤ d := by
  have h1 : primeSeq (Nat.count Nat.Prime p) = p := primeSeq_count hp
  have h2 : primeSeq (Nat.count Nat.Prime p + 1) ≤ p + d := by
    refine primeSeq_succ_le_of_prime hpd ?_
    rw [h1]; omega
  unfold primeGap
  omega

/-- A prime pair with shift `d` above any given bound produces a prime-gap index above any
given bound. -/

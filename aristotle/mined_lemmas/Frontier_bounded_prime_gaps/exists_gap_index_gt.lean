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

theorem exists_gap_index_gt (d : ℕ) (hd : 0 < d)
    (hinf : {p : ℕ | p.Prime ∧ (p + d).Prime}.Infinite) (N : ℕ) :
    ∃ n, N < n ∧ primeGap n ≤ d := by
  obtain ⟨p, hp, hpN⟩ := hinf.exists_gt (primeSeq N)
  refine ⟨Nat.count Nat.Prime p, ?_, primeGap_le_of_prime_pair hp.1 hp.2 hd⟩
  have hcount : primeSeq (Nat.count Nat.Prime p) = p := primeSeq_count hp.1
  have : primeSeq N < primeSeq (Nat.count Nat.Prime p) := by rw [hcount]; exact hpN
  exact (Nat.nth_lt_nth setOf_prime_infinite).1 this

/-- **Reduction**: infinitely many prime pairs with a common shift imply bounded prime gaps. -/

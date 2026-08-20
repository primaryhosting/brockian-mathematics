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

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`. -/

lemma nth_prime_le_nth_prime {m n : ℕ} (h : m ≤ n) :
    Nat.nth Nat.Prime m ≤ Nat.nth Nat.Prime n :=
  (Nat.nth_le_nth Nat.infinite_setOf_prime).2 h


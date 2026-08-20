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

lemma primeGap_pos (n : ℕ) : 0 < primeGap n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    nth_prime_lt_nth_prime (Nat.lt_succ_self n)
  simp only [primeGap]
  omega

/-- If `q` is a prime exceeding the `j`-th prime, then the `(j+1)`-st prime is at most `q`. -/

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

lemma primeGap_le_nth (n : ℕ) : primeGap n ≤ Nat.nth Nat.Prime n := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime n)
    (Nat.prime_nth_prime n).ne_zero
  have h3 : Nat.nth Nat.Prime (n + 1) ≤ q := nth_prime_succ_le_of_prime hq h1
  simp only [primeGap]
  omega

end Basic

section Reduction

/-- Infinitely many pairs of primes at distance at most `B` yield infinitely many indices `n`
with `p_{n+1} - p_n ≤ B`. -/

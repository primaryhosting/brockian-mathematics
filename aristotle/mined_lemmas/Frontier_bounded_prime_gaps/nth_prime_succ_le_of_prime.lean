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

lemma nth_prime_succ_le_of_prime {j q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime j < q) :
    Nat.nth Nat.Prime (j + 1) ≤ q := by
  classical
  have hjp : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
  have hcount : Nat.count Nat.Prime (Nat.nth Nat.Prime j) = j :=
    Nat.count_nth_of_infinite Nat.infinite_setOf_prime j
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime j + 1) = j + 1 := by
    rw [Nat.count_succ_eq_succ_count_iff.2 hjp, hcount]
  have h2 : j + 1 ≤ Nat.count Nat.Prime q := by
    rw [← h1]
    exact Nat.count_monotone _ h
  calc Nat.nth Nat.Prime (j + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        nth_prime_le_nth_prime h2
    _ = q := Nat.nth_count hq

/-- Bertrand's postulate gives the (trivial, unconditional) bound `p_{n+1} - p_n ≤ p_n`. -/

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

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

theorem bounded_prime_gaps_of_bounded_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  refine bounded_prime_gaps.1 ⟨B, fun N => ?_⟩
  obtain ⟨p, q, hple, hp, hq, hpq, hqB⟩ := h (nthPrime N + 1)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have hnp : nthPrime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have : nthPrime N < nthPrime (Nat.count Nat.Prime p) := by omega
    exact le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).1 this)
  · have hnp : nthPrime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have hsucc : nthPrime (Nat.count Nat.Prime p + 1) ≤ q :=
      nthPrime_succ_le_of_prime hq (by omega)
    simp only [primeGap, hnp]
    omega

/-- The twin prime conjecture implies that the liminf of the prime gaps is finite. -/

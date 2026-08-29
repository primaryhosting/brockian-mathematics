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

/-- `primeGap n = p_{n+1} - p_n`, the gap between the `n`-th and `(n+1)`-st prime
(with `p_0 = 2`, i.e. `p_n = Nat.nth Nat.Prime n`). -/

theorem exists_bound_frequently_gap_le (h : TwoPrimesInBoundedWindow) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ primeGap n ≤ B := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun N => ?_⟩
  obtain ⟨p, q, hp, hq, hNp, hpq, hqB⟩ := hB (Nat.nth Nat.Prime N + 1)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have hlt : Nat.nth Nat.Prime N < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
      rw [Nat.nth_count hp]; omega
    exact ((Nat.nth_lt_nth primes_infinite).1 hlt).le
  · have := nth_succ_count_le hp hq hpq
    rw [primeGap, Nat.nth_count hp]
    omega

/-- The set of indices with gap at most `B` is frequently hit, phrased with `Filter`. -/

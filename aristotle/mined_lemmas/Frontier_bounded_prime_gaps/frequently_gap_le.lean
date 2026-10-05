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

theorem frequently_gap_le (h : TwoPrimesInBoundedWindow) :
    ∃ B : ℕ, ∃ᶠ n in atTop, primeGap n ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_frequently_gap_le h
  refine ⟨B, ?_⟩
  rw [frequently_atTop]
  exact fun N => hB N

/-- **Bounded prime gaps** (Zhang / Maynard), stated as: the `liminf` of the sequence of
consecutive prime gaps is finite.

This is a Lean-checked *reduction*: the conclusion is derived from the
Goldston–Pintz–Yıldırım-type hypothesis `DHL2`, which is exactly what the sieve-theoretic
work of Zhang and Maynard establishes. -/

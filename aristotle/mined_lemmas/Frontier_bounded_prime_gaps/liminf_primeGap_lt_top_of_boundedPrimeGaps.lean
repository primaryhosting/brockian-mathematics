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

theorem liminf_primeGap_lt_top_of_boundedPrimeGaps (H : BoundedPrimeGaps) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  obtain ⟨B, hB⟩ := H
  have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
    have : ∃ᶠ n in atTop, primeGap n ≤ B := Nat.frequently_atTop_iff_infinite.2 hB
    exact this.mono fun n hn => by exact_mod_cast hn
  refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' hfreq) ?_
  exact WithTop.coe_lt_top (B : ℕ)

/-- Conversely, finiteness of the `liminf` of the prime gaps gives a bound attained
infinitely often, so the two formulations of bounded prime gaps agree. -/

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

theorem boundedPrimeGaps_iff_liminf_lt_top :
    BoundedPrimeGaps ↔ liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ :=
  ⟨liminf_primeGap_lt_top_of_boundedPrimeGaps, boundedPrimeGaps_of_liminf_primeGap_lt_top⟩

section BaseCases

/-- A prime `q` is the `n`-th prime as soon as exactly `n` primes are smaller than `q`. -/

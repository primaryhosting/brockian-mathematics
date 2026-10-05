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

theorem boundedPrimeGaps_of_infinitelyManyPrimePairs (H : InfinitelyManyPrimePairs) :
    BoundedPrimeGaps := by
  obtain ⟨d, hd, hinf⟩ := H
  refine ⟨d, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hgap⟩ := exists_gap_index_gt d hd hinf N
  exact absurd (hN hgap) (not_le.mpr hn)

end Reduction

/-- Bounded prime gaps, expressed as finiteness of `liminf (p_{n+1} - p_n)` in `ℕ∞`. -/

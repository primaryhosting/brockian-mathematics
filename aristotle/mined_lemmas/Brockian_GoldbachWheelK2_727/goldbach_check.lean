import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Brockian

/-- The Goldbach "wheel" statement with `K = 2` spokes at modulus `M`:
every even number `n` with `4 ≤ n ≤ 2 * M` is a sum of two primes. -/

private lemma goldbach_check :
    ∀ k ∈ Finset.range 728, 2 ≤ k →
      ∃ p ∈ wheelSmallPrimes, p ≤ 2 * k ∧ (2 * k - p) ∈ wheelPrimes := by
  decide


import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma primes_lt_eleven {p : ℕ} (hp : p.Prime) (h : p < 11) : p ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  have h2 := hp.two_le
  interval_cases p <;> revert hp <;> decide


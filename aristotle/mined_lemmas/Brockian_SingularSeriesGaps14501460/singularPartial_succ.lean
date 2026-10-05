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

lemma singularPartial_succ (H : Finset ℤ) (N : ℕ) :
    singularPartial H (N + 1) =
      singularPartial H N * (if (N + 1).Prime then localFactor H (N + 1) else 1) := by
  simp only [singularPartial, Finset.prod_filter]
  rw [Finset.prod_range_succ]


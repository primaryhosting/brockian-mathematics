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

lemma singularPartial_pos (N : ℕ) : 0 < singularPartial gapTuple N := by
  refine Finset.prod_pos fun p hp => ?_
  exact localFactor_pos (Finset.mem_filter.mp hp).2


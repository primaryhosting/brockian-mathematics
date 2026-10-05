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

lemma gapTuple_bounds : ∀ h ∈ gapTuple, (1451:ℤ) ≤ h ∧ h ≤ 1459 := by
  decide

/-- `nu H p` is the number of residue classes mod `p` occupied by the tuple `H`. -/

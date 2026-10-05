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

lemma gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact (exists_missing_iff gapTuple p).mpr (nu_gapTuple_lt hp)

/-! ## Bounds on the local factors -/


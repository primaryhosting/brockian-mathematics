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

lemma nu_gapTuple_lt {p : ℕ} (hp : p.Prime) : nu gapTuple p < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases h9 : 9 ≤ p
  · rw [nu_gapTuple_eq_four h9]; omega
  · exact (exists_missing_iff gapTuple p).mp ⟨0, zero_missing hp (by omega)⟩


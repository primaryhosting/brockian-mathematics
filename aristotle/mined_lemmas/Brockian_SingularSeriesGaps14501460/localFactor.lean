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

noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- The partial product of the singular series over all primes `≤ N`. -/

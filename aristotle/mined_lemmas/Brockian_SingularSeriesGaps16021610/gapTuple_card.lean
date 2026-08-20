/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - 1/p)^{-|H|} (1 - ν_p(H)/p)` is nonzero at every prime. -/

theorem gapTuple_card : gapTuple.card = 8 := by decide

/-- Every element of the pattern lies in the gap range `[0, 26]`, and the endpoints
of that range are attained, so the pattern has diameter exactly `26`. -/

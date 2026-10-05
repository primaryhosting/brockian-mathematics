/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the integers of `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

lemma nu_two_gapSet : nu 2 gapSet = 1 := by decide


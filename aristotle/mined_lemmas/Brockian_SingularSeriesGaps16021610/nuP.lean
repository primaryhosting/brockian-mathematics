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

/-- The gap pattern `(0, 1602, 1610)`, i.e. the triple of integer shifts
`{0, 1602, 1610}` (gaps `1602` and `1610` from the base point). -/

def nuP (p : ℕ) : ℕ := (gapSet16021610.image (fun h : ℤ => (h : ZMod p))).card

/-- For every prime `p`, the gap range `{0, 1602, 1610}` occupies fewer than `p`
residue classes mod `p`. -/

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

def gapSet16021610 : Finset ℤ := {0, 1602, 1610}

/--
**Admissibility of the gap range `(0, 1602, 1610)`.**

For every prime `p` there is a residue class mod `p` avoided by the triple
`{0, 1602, 1610}`; equivalently the triple does not cover all residues mod `p`
for any prime `p`, which is exactly the admissibility condition guaranteeing a
nonvanishing singular series `𝔖(H) ≠ 0` in the Hardy–Littlewood prime `k`-tuple
heuristic.
-/

/- (Lean requires `import` lines to precede any module docstring, so the mandated
header is reproduced verbatim inside this plain comment.)
/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian

/-- The local count of a `k`-tuple `H` of integers at a modulus `p`: the number of
distinct residue classes modulo `p` occupied by the entries of `H`. -/

theorem localCount_three_zero_two_six : localCount 3 ![0, 2, 6] = 2 := by
  decide

/-- **Constellation local count, k = 3.**  For every prime `p`:
the local count of any triple of integers is at most `3`, and the triple `(0, 2, 6)`
is locally admissible at `p`, i.e. it omits at least one residue class mod `p`.
Consequently `(0,2,6)` is an admissible constellation. -/

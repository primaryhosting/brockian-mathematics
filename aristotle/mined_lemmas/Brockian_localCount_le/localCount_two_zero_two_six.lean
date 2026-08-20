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

theorem localCount_two_zero_two_six : localCount 2 ![0, 2, 6] = 1 := by
  decide


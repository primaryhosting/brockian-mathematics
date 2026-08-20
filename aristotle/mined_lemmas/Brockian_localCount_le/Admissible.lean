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

def Admissible {k : ℕ} (H : Fin k → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → localCount p H < p

/-- The local count of a `k`-tuple never exceeds `k`. -/

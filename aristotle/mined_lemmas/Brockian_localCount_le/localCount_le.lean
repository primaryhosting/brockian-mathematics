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

theorem localCount_le {k : ℕ} (p : ℕ) (H : Fin k → ℤ) : localCount p H ≤ k := by
  refine le_trans (Finset.card_image_le) ?_
  simp


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

noncomputable def localCount {k : ℕ} (p : ℕ) (H : Fin k → ℤ) : ℕ :=
  (Finset.univ.image fun i => ((H i : ZMod p))).card

/-- A tuple is admissible when, for every prime `p`, it misses at least one residue class
modulo `p`. -/

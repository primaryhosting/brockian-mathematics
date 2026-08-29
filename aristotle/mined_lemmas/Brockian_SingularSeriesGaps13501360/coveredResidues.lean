/-
/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
(Lean requires the `import` command to be the very first command of a file, so
the header above is reproduced verbatim inside this comment and again as the
module docstring below.)
-/
import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- The set of residue classes modulo `p` that are occupied by the shift set `H`. -/

def coveredResidues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (h : ZMod p))

/-- A finite set of integer shifts (a "gap pattern") is *admissible* if for every prime `p`
it misses at least one residue class modulo `p`.  This is exactly the condition under which
the Hardy–Littlewood singular series of the tuple is nonzero. -/

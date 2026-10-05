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

noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (coveredResidues H p).card / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card

/-- For an admissible pattern every local factor of the singular series is strictly positive
(so no factor of the singular series vanishes). -/

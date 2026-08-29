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

def smallPrimeProduct (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p

/-- Concrete instance of the main theorem: for every `k`, the arithmetic progression of
length `k` starting at `1` with common difference the product of all primes `≤ k` is an
admissible pattern. -/

/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if, for every prime `p`, it fails to cover
all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series of the tuple is nonzero. -/

noncomputable def singularSeriesFactor (d : ℤ) : ℝ :=
  if Even d ∧ d ≠ 0 then
    ∏ p ∈ d.natAbs.primeFactors.erase 2, ((p : ℝ) - 1) / ((p : ℝ) - 2)
  else 0

section Basic

/-- Pigeonhole: a set with fewer than `p` elements misses a residue class mod `p`. -/

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

theorem singularSeriesFactor_eq_zero_of_odd {d : ℤ} (hodd : ¬ Even d) :
    singularSeriesFactor d = 0 := by
  rw [singularSeriesFactor, if_neg]
  exact fun h => hodd h.1

/-- Positivity of the singular series factor characterises admissible gaps. -/

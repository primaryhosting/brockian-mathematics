/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma ev_ne_zero (a : Fin n) : ev a ≠ 0 := by
  simp only [ev]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)


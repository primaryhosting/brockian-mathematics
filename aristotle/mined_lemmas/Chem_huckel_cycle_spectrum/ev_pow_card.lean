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

lemma ev_pow_card (a : Fin n) : ev a ^ n = 1 := by
  simp only [ev, ← pow_mul, mul_comm ((a : ℕ)) n, pow_mul, zeta_pow_self, one_pow]


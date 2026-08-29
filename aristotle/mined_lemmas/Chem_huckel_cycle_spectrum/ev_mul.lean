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

lemma ev_mul (a b : Fin n) : ev (a * b) = ev b ^ (a : ℕ) := by
  simp only [ev, Fin.val_mul, zeta_pow_mod, ← pow_mul, mul_comm]


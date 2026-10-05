import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma dftMatrix_apply {n : ℕ} (j k : Fin n) :
    dftMatrix n j k = zeta n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [dftMatrix, Matrix.vandermonde_apply, ← pow_mul]


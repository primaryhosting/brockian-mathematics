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

lemma dftMatrix_det_ne_zero {n : ℕ} (hn : n ≠ 0) : (dftMatrix n).det ≠ 0 := by
  rw [dftMatrix, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext ((isPrimitiveRoot_zeta hn).pow_inj a.isLt b.isLt hab)

/-- The diagonal matrix of Hückel energies `2 cos (2πk/n)`. -/

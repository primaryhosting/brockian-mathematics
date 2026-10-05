/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma dftMat_apply (j k : Fin 17) : dftMat j k = zeta17 ^ ((j : ℕ) * (k : ℕ)) := by
  simp [dftMat, pow_mul]

/-- The list of Hückel eigenvalues of the cycle `C₁₇`. -/

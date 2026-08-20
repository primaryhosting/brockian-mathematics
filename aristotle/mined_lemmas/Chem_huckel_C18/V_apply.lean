/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma V_apply (j k : Fin 18) : V j k = om ^ ((j : ℕ) * (k : ℕ)) := by
  simp [V, Matrix.vandermonde, pow_mul]

/-- The diagonal matrix of Hückel eigenvalues of `C₁₈`. -/

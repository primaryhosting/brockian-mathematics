/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem C11fourier_apply (k i : Fin 11) : C11fourier k i = zeta11 ^ ((k : ℕ) * (i : ℕ)) := by
  rw [C11fourier, Matrix.vandermonde_apply, ← pow_mul]


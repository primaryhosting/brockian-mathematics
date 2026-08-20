/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma vandermonde_apply_eq (i k : Fin 16) :
    (Matrix.vandermonde node16) i k = node16 k ^ (i : ℕ) := by
  simp only [Matrix.vandermonde_apply, node16, ← pow_mul, mul_comm]


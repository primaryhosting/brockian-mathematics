import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma ee_pow_eleven (m : Fin 11) : ee m ^ 11 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_eleven, one_pow]


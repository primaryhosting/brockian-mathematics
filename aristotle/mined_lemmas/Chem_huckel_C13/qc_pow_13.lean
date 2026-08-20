import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma qc_pow_13 (k : Fin 13) : (qc k) ^ 13 = 1 := by
  rw [qc, ← pow_mul, mul_comm, pow_mul, zeta13_pow_13, one_pow]


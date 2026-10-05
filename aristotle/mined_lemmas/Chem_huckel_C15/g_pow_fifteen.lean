import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma g_pow_fifteen (i : Fin 15) : (g i) ^ 15 = 1 := by
  unfold g
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_fifteen, one_pow]


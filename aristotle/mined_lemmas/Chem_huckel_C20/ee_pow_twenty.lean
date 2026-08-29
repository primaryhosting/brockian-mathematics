import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma ee_pow_twenty (m : Fin 20) : (ee m) ^ 20 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_twenty, one_pow]


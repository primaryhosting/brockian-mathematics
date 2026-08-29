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

lemma ee_mul_pow (m k : Fin 20) : ee (m * k) = (ee m) ^ (k : ℕ) := by
  simp only [ee, Fin.val_mul, zeta_pow_mod, pow_mul]


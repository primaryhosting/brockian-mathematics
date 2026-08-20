import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma ee_mul (a b : Fin 7) : ee (a * b) = (ee b) ^ (a.val) := by
  simp only [ee, Fin.val_mul, zeta_pow_mod]
  rw [Nat.mul_comm, pow_mul]


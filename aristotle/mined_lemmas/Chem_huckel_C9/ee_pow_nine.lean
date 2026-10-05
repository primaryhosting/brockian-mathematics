import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma ee_pow_nine (c : ZMod 9) : (ee c) ^ 9 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]

/-- Orthogonality of characters on `ZMod 9`. -/

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

lemma ee_pow (c j : ZMod 9) : ee (c * j) = (ee c) ^ j.val := by
  simp only [ee, ZMod.val_mul, om_pow_mod, pow_mul]


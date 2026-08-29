import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma ee_mul (j c : ZMod 18) : ee (j * c) = ee c ^ j.val := by
  rw [← ee_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]


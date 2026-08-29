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

lemma ee_pow_18 (c : ZMod 18) : ee c ^ 18 = 1 := by
  rw [← ee_nsmul, nsmul_eq_mul, show ((18 : ℕ) : ZMod 18) = 0 from ZMod.natCast_self 18,
    zero_mul, ee_zero]


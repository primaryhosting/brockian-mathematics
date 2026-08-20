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

lemma zeta_pow_eleven : zeta ^ 11 = 1 := zeta_primitive.pow_eq_one

/-- The character `m ↦ ζ^m` of `Fin 11 = ZMod 11`. -/

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

lemma zeta_primitive : IsPrimitiveRoot zeta 11 := Complex.isPrimitiveRoot_exp 11 (by norm_num)


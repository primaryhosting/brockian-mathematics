import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma zeta8_prim : IsPrimitiveRoot zeta8 8 := by
  simpa [zeta8] using Complex.isPrimitiveRoot_exp 8 (by norm_num)


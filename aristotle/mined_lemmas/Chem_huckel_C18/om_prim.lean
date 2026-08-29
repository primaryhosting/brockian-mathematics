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

lemma om_prim : IsPrimitiveRoot om 18 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 18 (by norm_num)


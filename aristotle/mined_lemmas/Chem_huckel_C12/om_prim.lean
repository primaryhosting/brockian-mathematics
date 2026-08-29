import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma om_prim : IsPrimitiveRoot om 12 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 12 (by norm_num)


import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma zeta9_pow_nine : zeta9 ^ 9 = 1 := zeta9_isPrimitiveRoot.pow_eq_one


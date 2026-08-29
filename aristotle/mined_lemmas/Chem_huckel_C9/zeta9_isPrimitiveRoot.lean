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

lemma zeta9_isPrimitiveRoot : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)


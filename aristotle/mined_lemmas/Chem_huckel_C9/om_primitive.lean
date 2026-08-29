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

lemma om_primitive : IsPrimitiveRoot om 9 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 9 (by norm_num)


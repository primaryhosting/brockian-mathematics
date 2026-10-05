import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma w_isPrimitiveRoot : IsPrimitiveRoot w 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [w] using this


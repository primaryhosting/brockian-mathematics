import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 7 := by
  have h := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  norm_num at h
  simpa [zeta] using h


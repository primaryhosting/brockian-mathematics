import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma isPrimitiveRoot_omega19 : IsPrimitiveRoot omega19 19 := by
  simpa [omega19] using Complex.isPrimitiveRoot_exp 19 (by norm_num)


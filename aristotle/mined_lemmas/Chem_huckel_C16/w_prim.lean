/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma w_prim : IsPrimitiveRoot w 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [w] using this


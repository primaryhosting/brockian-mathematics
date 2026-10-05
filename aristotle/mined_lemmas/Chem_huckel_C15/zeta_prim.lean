import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma zeta_prim : IsPrimitiveRoot zeta 15 := by
  have := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [zeta] using this


/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma U_apply (j k : Fin 20) : U j k = evec k j := by
  simp [U, Matrix.vandermonde, evec, ← pow_mul]


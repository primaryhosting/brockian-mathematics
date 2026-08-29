/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

lemma U_det_ne_zero : U.det ≠ 0 := by
  rw [U, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_primitive.pow_inj i.isLt j.isLt hij)

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/15)`. -/

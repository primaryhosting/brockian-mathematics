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

lemma U_apply (i k : Fin 15) : U i k = zeta ^ ((i : ℕ) * (k : ℕ)) := by
  rw [U, Matrix.vandermonde_apply, ← pow_mul]


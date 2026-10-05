/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma Gmat_mul_C8adj : Gmat * C8adj = Matrix.diagonal mu * Gmat := by
  calc Gmat * C8adj = Gmat * C8adj * (Fmat * Gmat) := by rw [Fmat_mul_Gmat, mul_one]
    _ = Gmat * (C8adj * Fmat) * Gmat := by simp [mul_assoc]
    _ = Gmat * (Fmat * Matrix.diagonal mu) * Gmat := by rw [C8adj_mul_Fmat]
    _ = Matrix.diagonal mu * Gmat := by
        rw [← mul_assoc Gmat Fmat, Gmat_mul_Fmat, one_mul]

/-- The exponential form of the eigenvalue is the familiar `2 cos (2πk/8)`. -/

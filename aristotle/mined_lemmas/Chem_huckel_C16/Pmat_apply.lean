import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma Pmat_apply (i k : ZMod 16) : Pmat i k = zeta ^ (i.val * k.val) := by
  simp [Pmat, Matrix.vandermonde, ← pow_mul]
  rfl


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

lemma C16_mul_Pmat : C16 * Pmat = Pmat * Matrix.diagonal huckelEigenvalue := by
  ext i k
  rw [Matrix.mul_diagonal]
  have hmul : (C16 * Pmat) i k = C16.mulVec (fun j => Pmat j k) i := rfl
  rw [hmul, C16_mulVec, Pmat_apply, Pmat_apply, Pmat_apply]
  have hz : zeta ^ k.val ≠ 0 := pow_ne_zero _ zeta_ne_zero
  apply mul_right_cancel₀ hz
  rw [add_mul, zeta_pred, zeta_succ, mul_assoc, mul_assoc, huckelEigenvalue_mul]
  ring


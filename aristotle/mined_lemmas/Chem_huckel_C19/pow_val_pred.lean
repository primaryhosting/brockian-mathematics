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

lemma pow_val_pred (w : ℂ) (hw : w ^ 19 = 1) (hw0 : w ≠ 0) (i : Fin 19) :
    w ^ ((i - 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w⁻¹ := by
  have h := pow_val_succ w hw (i - 1)
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv_cancel₀ hw0, mul_one]


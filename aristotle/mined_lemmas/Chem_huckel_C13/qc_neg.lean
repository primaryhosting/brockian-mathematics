import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma qc_neg (a : Fin 13) : qc (-a) = (qc a)⁻¹ := by
  have h : qc a * qc (-a) = 1 := by rw [← qc_add]; simp [qc_zero]
  exact eq_inv_of_mul_eq_one_left (by linear_combination h)


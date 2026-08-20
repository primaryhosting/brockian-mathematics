/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma dftP_mul_dftQ : dftP * dftQ = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 19, dftP a j * dftQ j b
      = (19 : ℂ)⁻¹ * (zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹) := by
    intro j; simp only [dftP, dftQ]; ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, dft_sum]
  by_cases hab : a = b <;> simp [hab, Matrix.one_apply]


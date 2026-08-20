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

lemma dftQ_mul_dftP : dftQ * dftP = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 19, dftQ a j * dftP j b
      = (19 : ℂ)⁻¹ * (zeta ^ (b.val * j.val) * (zeta ^ (j.val * a.val))⁻¹) := by
    intro j
    simp only [dftP, dftQ]
    rw [mul_comm a.val j.val, mul_comm j.val b.val]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, dft_sum]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Ne.symm hab, hab]


/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma det_F5_ne_zero : F5.det ≠ 0 := by
  intro h
  have : F5.det * G5.det = 1 := by
    rw [← Matrix.det_mul, F5_mul_G5, Matrix.det_one]
  rw [h, zero_mul] at this
  exact zero_ne_one this


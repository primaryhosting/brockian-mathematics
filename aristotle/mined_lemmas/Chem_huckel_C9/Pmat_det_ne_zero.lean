import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  intro h
  have h2 : (Pmat * Qmat).det = 0 := by rw [Matrix.det_mul, h, zero_mul]
  rw [Pmat_mul_Qmat] at h2
  simp at h2


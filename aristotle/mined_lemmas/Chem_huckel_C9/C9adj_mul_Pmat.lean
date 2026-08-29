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

lemma C9adj_mul_Pmat : C9adj * Pmat = Pmat * Matrix.diagonal eig := by
  ext i k
  have h := C9adj_mulVec (fun j => Pmat j k) i
  simp only [Matrix.mulVec, dotProduct] at h
  rw [Matrix.mul_apply, h, Matrix.mul_diagonal]
  simp only [Pmat, Matrix.of_apply]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + (-k) by ring,
    ee_add, ee_add, ← mul_add, ee_add_ee_neg]


import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma C11_mul_F : C11 * F = F * Matrix.diagonal eig := by
  ext i k
  rw [Matrix.mul_diagonal]
  have hcol : (C11 * F) i k = (C11 *ᵥ (fun j => F j k)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcol, C11_mulVec]
  have e1 : F (i + 1) k = F i k * ch k := by
    rw [F, F, ← ch_add]; congr 1; ring
  have e2 : F (i - 1) k = F i k * ch (-k) := by
    rw [F, F, ← ch_add]; congr 1; ring
  rw [e1, e2, ← mul_add, ch_add_ch_neg]

/-- Explicit eigenvectors: the Bloch wave `j ↦ exp (2πI jk/11)` is an eigenvector of the
adjacency matrix of `C₁₁` with eigenvalue `2 cos (2πk/11)`. -/

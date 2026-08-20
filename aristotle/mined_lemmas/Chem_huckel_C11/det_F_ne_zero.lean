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

lemma det_F_ne_zero : F.det ≠ 0 := by
  intro h
  have h2 : F.det * G.det = (11 : ℂ) ^ 11 := by
    rw [← Matrix.det_mul, F_mul_G, Matrix.det_smul, Matrix.det_one, mul_one]
    norm_num
  rw [h, zero_mul] at h2
  norm_num at h2


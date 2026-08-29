import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma dft_det_ne_zero : dft.det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det dft_mul_dftInv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
  have hcard : Fintype.card (ZMod 13) = 13 := by simp
  rw [hcard] at h2
  norm_num at h2


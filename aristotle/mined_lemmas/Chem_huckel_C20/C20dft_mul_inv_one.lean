/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20dft_mul_inv_one : C20dft * ((20 : ℂ)⁻¹ • C20dftInv) = 1 := by
  rw [Matrix.mul_smul, C20dft_mul_inv, smul_smul]
  norm_num

/-- The Fourier matrix as a unit of the matrix ring. -/

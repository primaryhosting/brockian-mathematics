import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma det_C16_sub (mu : ℂ) :
    (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)).det
      = ∏ k : ZMod 16, (huckelEigenvalue k - mu) := by
  have hcomm : (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)) * Pmat
      = Pmat * (Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)) := by
    rw [sub_mul, mul_sub, C16_mul_Pmat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdiag : Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)
      = Matrix.diagonal (fun k => huckelEigenvalue k - mu) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
  have h := congrArg Matrix.det hcomm
  rw [Matrix.det_mul, Matrix.det_mul, hdiag, Matrix.det_diagonal] at h
  apply mul_right_cancel₀ Pmat_det_ne_zero
  rw [h, mul_comm]

/-- **Hückel theory for the C₁₆ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₆` if and only if it is of the form
`2·cos(2πk/16)` for some `k ∈ {0, …, 15}`. -/

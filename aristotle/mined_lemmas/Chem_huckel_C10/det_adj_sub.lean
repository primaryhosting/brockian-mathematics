import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem det_adj_sub (mu : ℂ) :
    (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)).det
      = ∏ k : ZMod 10, (C10eigen k - mu) := by
  have key : (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)) * C10F
      = C10F * Matrix.diagonal (fun k => C10eigen k - mu) := by
    have hd : Matrix.diagonal (fun k => C10eigen k - mu)
        = Matrix.diagonal C10eigen - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ) := by
      ext a b
      rcases eq_or_ne a b with hab | hab
      · simp [hab]
      · simp [hab]
    rw [hd, Matrix.sub_mul, Matrix.mul_sub, adj_mul_C10F, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ C10F_det_ne_zero (by rw [hdet]; ring :
    (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)).det * C10F.det
      = (∏ k : ZMod 10, (C10eigen k - mu)) * C10F.det)
  exact this

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ω^{jk}` is an eigenvector of the
adjacency matrix of `C₁₀` with eigenvalue `2 cos (2πk/10)`. -/

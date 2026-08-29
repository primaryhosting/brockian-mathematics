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

lemma det_adj_sub (lam : ℂ) :
    (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det = ∏ k : ZMod 13, (mu k - lam) := by
  have key : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) * dft =
      dft * (Matrix.diagonal mu - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) := by
    rw [sub_mul, mul_sub, adj_mul_dft, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h1 : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det =
      (Matrix.diagonal mu - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det := by
    exact mul_right_cancel₀ dft_det_ne_zero (hdet.trans (mul_comm _ _))
  rw [h1, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal]


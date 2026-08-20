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

lemma det_sub_smul (μ : ℂ) :
    (C11 - μ • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)).det = ∏ k : ZMod 11, (eig k - μ) := by
  have hmul : (C11 - μ • 1) * F = F * Matrix.diagonal (fun k => eig k - μ) := by
    have hd : Matrix.diagonal (fun k => eig k - μ)
        = Matrix.diagonal eig - μ • (1 : Matrix (ZMod 11) (ZMod 11) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, Matrix.sub_mul, Matrix.mul_sub, C11_mul_F, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_F_ne_zero (by rw [hdet]; ring :
    (C11 - μ • 1).det * F.det = (∏ k : ZMod 11, (eig k - μ)) * F.det)
  exact this

/-- **Hückel theory for the cycle `C₁₁`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₁`
(i.e. there is a nonzero vector `v` with `A v = μ v`) if and only if
`μ = 2 cos (2πk/11)` for some `k ∈ {0, 1, …, 10}`. -/

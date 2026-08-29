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

lemma det_sub_smul (μ : ℂ) :
    (C9adj - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)).det = ∏ k : ZMod 9, (eig k - μ) := by
  have hd : Matrix.diagonal (fun k : ZMod 9 => eig k - μ)
      = Matrix.diagonal eig - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have key : (C9adj - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)) * Pmat
      = Pmat * Matrix.diagonal (fun k : ZMod 9 => eig k - μ) := by
    rw [hd, sub_mul, mul_sub, C9adj_mul_Pmat, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  exact mul_right_cancel₀ Pmat_det_ne_zero (by rw [hdet]; ring)

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₉`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₉` (vertices `ZMod 9`, with `i` adjacent to `i ± 1`)
if and only if `μ = 2 cos (2πk/9)` for some `k ∈ {0, 1, …, 8}`. -/

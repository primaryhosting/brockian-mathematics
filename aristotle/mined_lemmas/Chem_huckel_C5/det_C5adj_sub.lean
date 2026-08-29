/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

theorem det_C5adj_sub (mu : ℂ) :
    (C5adj - mu • 1).det = ∏ k : ZMod 5, (huckelEigenvalue k - mu) := by
  have key : (C5adj - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)) * F5
      = F5 * (Matrix.diagonal huckelEigenvalue - mu • 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, C5adj_mul_F5]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hd : (Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ))
      = Matrix.diagonal (fun k => huckelEigenvalue k - mu) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [hd, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_F5_ne_zero (by rw [hdet]; ring :
    (C5adj - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)).det * F5.det
      = (∏ k : ZMod 5, (huckelEigenvalue k - mu)) * F5.det)
  exact this

/-! ### Eigenvectors -/

/-- The `k`-th Hückel eigenvector of `C₅`. -/

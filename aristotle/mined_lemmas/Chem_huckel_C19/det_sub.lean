/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma det_sub (mu : ℂ) :
    (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj).det
      = ∏ k : ZMod 19, (mu - C19eig k) := by
  have hdiag : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) - Matrix.diagonal C19eig
      = Matrix.diagonal (fun k => mu - C19eig k) := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
    split <;> simp
  have hcomm : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) * C19vec
      = C19vec * (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) :=
    Algebra.commutes mu C19vec
  have hmul : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj) * C19vec
      = C19vec * Matrix.diagonal (fun k => mu - C19eig k) := by
    rw [← hdiag, Matrix.sub_mul, Matrix.mul_sub, hcomm, adj_mul_vec]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_vec_ne_zero (by rw [hdet]; ring :
    (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj).det * C19vec.det
      = (∏ k : ZMod 19, (mu - C19eig k)) * C19vec.det)
  exact this

/-! ### Main theorem -/

/-- **Hückel theory for `C₁₉`.** The eigenvalues (spectrum) of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, 1, …, 18`. -/

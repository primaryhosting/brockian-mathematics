/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/

lemma det_sub (z : ℂ) :
    ((algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z - C19adj).det
      = ∏ k : ZMod 19, (z - mu k) := by
  have hz : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z
      = Fm * diagonal (fun _ : ZMod 19 => z) * Gm := by
    have hd : (diagonal (fun _ : ZMod 19 => z)) = z • (1 : Matrix (ZMod 19) (ZMod 19) ℂ) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Fm_mul_Gm,
      Algebra.algebraMap_eq_smul_one]
  have hdiff : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z - C19adj
      = Fm * diagonal (fun k : ZMod 19 => z - mu k) * Gm := by
    rw [hz, C19adj_eq, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  rw [hdiff, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [mul_comm Fm.det _, mul_assoc, det_Fm_mul_det_Gm, mul_one]

/-- **Hückel spectrum of the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, …, 18`. -/

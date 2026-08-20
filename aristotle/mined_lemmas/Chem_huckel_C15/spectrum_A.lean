/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₅` has Hamiltonian `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₅`.  We show that the spectrum of `A` is exactly
`{2 cos (2πk/15) : k = 0, …, 14}`, by explicitly diagonalizing `A` with the discrete
Fourier matrix.
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

theorem spectrum_A : spectrum ℂ A = Set.range lam := by
  have hdetPQ : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, P_mul_Q, Matrix.det_one]
  ext μ
  have hM : (algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)) μ - A
      = P * Matrix.diagonal (fun k => μ - lam k) * Q := by
    rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← A_eq]
    congr 1
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, P_mul_Q,
      Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
    rfl
  have hdet : ((algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)) μ - A).det = ∏ k, (μ - lam k) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc P.det * (∏ k, (μ - lam k)) * Q.det
        = P.det * Q.det * ∏ k, (μ - lam k) := by ring
      _ = ∏ k, (μ - lam k) := by rw [hdetPQ, one_mul]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero, not_not,
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, Finset.mem_univ k, sub_self _⟩

/-- The explicit Hückel eigenvectors: the discrete Fourier mode `j ↦ ω^(jk)` is an eigenvector
of the adjacency matrix of `C₁₅` with eigenvalue `2 cos (2πk/15)`. -/

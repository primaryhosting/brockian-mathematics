import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

theorem huckel_C11_charpoly :
    ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).charpoly
      = ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℂ))) := by
  have hQP : dftMatrixInv * dftMatrix = 1 := mul_eq_one_comm.mp dft_mul_inv
  let U : (Matrix (Fin 11) (Fin 11) ℂ)ˣ := ⟨dftMatrix, dftMatrixInv, dft_mul_inv, hQP⟩
  have hA : (SimpleGraph.cycleGraph 11).adjMatrix ℂ
      = U.val * Matrix.diagonal huckelEigenvalue * (U⁻¹).val := by
    show (SimpleGraph.cycleGraph 11).adjMatrix ℂ
      = dftMatrix * Matrix.diagonal huckelEigenvalue * dftMatrixInv
    calc (SimpleGraph.cycleGraph 11).adjMatrix ℂ
        = (SimpleGraph.cycleGraph 11).adjMatrix ℂ * (dftMatrix * dftMatrixInv) := by
          rw [dft_mul_inv, mul_one]
      _ = ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix) * dftMatrixInv := by
          rw [mul_assoc]
      _ = dftMatrix * Matrix.diagonal huckelEigenvalue * dftMatrixInv := by rw [adj_mul_dft]
  rw [hA, Matrix.charpoly_units_conj U, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel theory for `C₁₁`.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₁` are exactly the numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/

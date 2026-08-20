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

lemma adj_mul_dft :
    (SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix
      = dftMatrix * Matrix.diagonal huckelEigenvalue := by
  have hne : ∀ j : Fin 11, j - 1 ≠ j + 1 := by decide
  ext j k
  have hrow : ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix) j k
      = dftMatrix (j - 1) k + dftMatrix (j + 1) k := by
    rw [Matrix.mul_apply]
    have h2 : ∑ l, ((SimpleGraph.cycleGraph 11).adjMatrix ℂ) j l * dftMatrix l k
        = ∑ l ∈ (SimpleGraph.cycleGraph 11).neighborFinset j, dftMatrix l k := by
      rw [← SimpleGraph.adjMatrix_mulVec_apply]
      rfl
    rw [h2, SimpleGraph.cycleGraph_neighborFinset (n := 9) (v := j),
      Finset.sum_pair (hne j)]
  rw [hrow, Matrix.mul_diagonal]
  simp only [dftMatrix]
  rw [fin11_ring2, fin11_ring3, ee_add, ee_add, ← mul_add, add_comm (ee (-k)) (ee k),
    ee_add_ee_neg]

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₁₁`
factors as `∏ k, (X - 2cos(2πk/11))`, i.e. the Hückel eigenvalues, with multiplicity,
are `2 cos (2πk/11)` for `k = 0, …, 10`. -/

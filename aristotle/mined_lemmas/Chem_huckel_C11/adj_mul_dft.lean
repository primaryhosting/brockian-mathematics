/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma adj_mul_dft :
    (SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMat = dftMat * eigDiag := by
  ext i k
  have hmul : ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMat) i k
      = ∑ u ∈ (SimpleGraph.cycleGraph 11).neighborFinset i, dftMat u k := by
    rw [Matrix.mul_apply]
    rw [← SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (G := SimpleGraph.cycleGraph 11) i
      (fun u => dftMat u k)]
    rfl
  rw [hmul, SimpleGraph.cycleGraph_neighborFinset (n := 9)]
  rw [Finset.sum_pair (fin11_sub_one_ne_add_one i)]
  simp only [dftMat, eigDiag, Matrix.of_apply, Matrix.mul_diagonal]
  rw [fin11_sub_one_mul, fin11_add_one_mul, echar_add, echar_add, ← mul_add,
    add_comm (echar (-k)) (echar k), echar_add_echar_neg]

/-- **Hückel theory for the C₁₁ ring.** The characteristic polynomial of the adjacency matrix
of the cycle graph `C₁₁` factors as `∏_{k=0}^{10} (X - 2 cos (2πk/11))`, i.e. the adjacency
eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0, …, 10`. -/

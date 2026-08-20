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

lemma A_mul_P : A * P = P * Matrix.diagonal lam := by
  ext j k
  have hne : (j - 1 : Fin 15) ≠ j + 1 := by revert j; decide
  have h : (A * P) j k = (A *ᵥ (fun m => P m k)) j := rfl
  have hnf : (SimpleGraph.cycleGraph 15).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 13)
  rw [h, A, SimpleGraph.adjMatrix_mulVec_apply, hnf, Finset.sum_pair hne, P_pred, P_succ,
    Matrix.mul_diagonal, ← om_pow_add_inv k]
  ring


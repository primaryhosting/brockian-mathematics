/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

lemma C10adj_mul_dftU : C10adj * dftU = dftU * C10diag := by
  rw [C10diag_eq]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp +decide [C10adj, dftU, Matrix.mul_apply, Fin.sum_univ_succ,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, zeta_pow_sub_ten,
      cycleGraph10_card_neighbors] <;>
    ring_nf <;>
    simp only [zeta_pow_sub_ten, Nat.reduceSub, Nat.reduceLeDiff] <;>
    ring1

/-- The characteristic polynomial of the adjacency matrix of `C₁₀` splits as
`∏_{k=0}^{9} (X - 2 cos (2πk/10))`; in particular the ten Hückel eigenvalues, listed with
multiplicity, are `2 cos (2πk/10)` for `k = 0, …, 9`. -/

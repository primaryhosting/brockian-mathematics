/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for `C₉`

The Hückel matrix of the cycle `C₉` (in units where the Coulomb integral is `0` and the
resonance integral is `1`) is the adjacency matrix of `SimpleGraph.cycleGraph 9`.
This file diagonalizes it by the discrete Fourier transform (a Vandermonde matrix built from
a primitive ninth root of unity) and computes its characteristic polynomial and spectrum:
the eigenvalues are `2 cos (2πk/9)`, `k = 0, …, 8`.
-/

open Matrix Polynomial SimpleGraph

namespace Chem

/-- A primitive ninth root of unity. -/

lemma A9_mul_F9 : A9 * F9 = F9 * Matrix.diagonal lam := by
  ext i j
  have hmv : (A9 * F9) i j = (A9 *ᵥ (fun l => F9 l j)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hmv, A9, SimpleGraph.adjMatrix_mulVec_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 7) (v := i),
    Finset.sum_pair (fin9_pair_ne i),
    Matrix.mul_diagonal, F9_apply, F9_apply, F9_apply, lam_eq, mul_add, ← pow_add, ← pow_add,
    fin9_sub_one, add_comm (zeta ^ ((i : ℕ) * (j : ℕ) + (j : ℕ)))]
  congr 1
  · exact zeta_pow_congr (by rw [Fin.val_add]; simpa using shift_mod i j 8)
  · exact zeta_pow_congr (by rw [Fin.val_add]; simpa using shift_mod i j 1)


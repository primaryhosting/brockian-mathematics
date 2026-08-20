/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Hückel theory for the cycle `C₇`

In Hückel molecular orbital theory the (reduced) Hamiltonian of a conjugated
cyclic polyene `Cₙ` is the adjacency matrix of the cycle graph `Cₙ`, and the
orbital energies are `α + β λ` where `λ` runs over the adjacency eigenvalues.
For `n = 7` (the cycloheptatrienyl system) the eigenvalues are
`2 cos (2πk/7)`, `k = 0, …, 6`.

The proof diagonalises the adjacency matrix by the discrete Fourier
(Vandermonde) matrix built from `ω = exp (2πi/7)`.
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The primitive 7-th root of unity `ω = exp (2πi/7)`. -/

theorem adj_mul_V : ((cycleGraph 7).adjMatrix ℂ) * V = V * Matrix.diagonal huckelVal := by
  ext i k
  have hne : (i - 1 : Fin 7) ≠ i + 1 := by revert i; decide
  have h1 : ((i + 1 : Fin 7) : ℕ) = ((i : ℕ) + 1) % 7 := by revert i; decide
  have h2 : ((i - 1 : Fin 7) : ℕ) = ((i : ℕ) + 6) % 7 := by revert i; decide
  have hz : (om ^ (k : ℕ)) ^ 7 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, om_pow_seven, one_pow]
  have hsum : (((cycleGraph 7).adjMatrix ℂ) * V) i k = V (i - 1) k + V (i + 1) k := by
    rw [Matrix.mul_apply, show (∑ j, ((cycleGraph 7).adjMatrix ℂ) i j * V j k) =
      ((cycleGraph 7).adjMatrix ℂ *ᵥ fun j => V j k) i from rfl,
      SimpleGraph.adjMatrix_mulVec_apply,
      show ((cycleGraph 7).neighborFinset i) = {i - 1, i + 1} from
        SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]
  rw [hsum, Matrix.mul_diagonal, V_apply, V_apply, V_apply, h1, h2,
    pow_mod_seven _ hz, pow_mod_seven _ hz, ← om_add_inv k, pow_add, pow_add]
  ring


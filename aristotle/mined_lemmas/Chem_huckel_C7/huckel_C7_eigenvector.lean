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

theorem huckel_C7_eigenvector (k : Fin 7) :
    ((cycleGraph 7).adjMatrix ℂ) *ᵥ (fun j : Fin 7 => (om ^ (k : ℕ)) ^ (j : ℕ))
      = ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) •
          (fun j : Fin 7 => (om ^ (k : ℕ)) ^ (j : ℕ)) := by
  funext i
  have h := congrFun (congrFun adj_mul_V i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, V_apply] at h
  simpa [Matrix.mulVec, dotProduct, V_apply, huckelVal, mul_comm] using h

/-- The set of adjacency eigenvalues (roots of the characteristic polynomial) of
`C₇` is exactly `{2 cos (2πk/7) : k = 0, …, 6}`. -/

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

theorem V_det_ne_zero : V.det ≠ 0 := by
  rw [V, Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero.mpr ?_
  intro hcon
  exact absurd (Fin.ext (om_primitive.pow_inj j.isLt i.isLt hcon)) (ne_of_gt hj)

/-- **Hückel theory for the cycle `C₇` (the cycloheptatrienyl system).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₇`
factors as `∏ₖ (X - 2 cos (2πk/7))`, `k = 0, …, 6`; that is, the adjacency
eigenvalues of `C₇` are exactly the seven numbers `2 cos (2πk/7)`, counted with
multiplicity. -/

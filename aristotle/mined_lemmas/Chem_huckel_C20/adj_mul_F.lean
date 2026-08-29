import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma adj_mul_F : (cycleGraph 20).adjMatrix ℂ * F = F * Matrix.diagonal hval := by
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, neighbor_sum, F_shift_add, F_shift_sub,
    Matrix.mul_diagonal, ← mul_add, add_comm (w ^ (19 * (k : ℕ))), w_add_inv]

/-- **Hückel theory for C₂₀.**  The spectrum of the adjacency matrix of the cycle graph
`C₂₀` is exactly `{2 cos (2πk/20) : k = 0, …, 19}`. -/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
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

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

theorem huckel_C6 :
    ((SimpleGraph.cycleGraph 6).adjMatrix ℝ).charpoly =
      ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 6))) := by
  rw [adjMatrix_cycleGraph_six, charpoly_A6]
  exact Finset.prod_congr rfl fun k _ => by rw [eig6_eq_cos k]

/-- The spectrum of the adjacency matrix of `C₆` is exactly the set of numbers
`2 cos (2πk/6)`, `k = 0, …, 5`. -/

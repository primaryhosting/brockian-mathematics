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

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma adj_mulVec (v : Fin 15 → ℂ) (j : Fin 15) :
    ((cycleGraph 15).adjMatrix ℂ).mulVec v j = v (j - 1) + v (j + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have h : (cycleGraph 15).neighborFinset j = {j - 1, j + 1} := cycleGraph_neighborFinset
  have hne : j - 1 ≠ j + 1 := by revert j; decide
  rw [h, Finset.sum_pair hne]

/-- **Hückel theory for the cyclic polyene C₁₅.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₅`
if and only if `μ = 2 cos (2πk/15)` for some `k ∈ {0, …, 14}`. -/

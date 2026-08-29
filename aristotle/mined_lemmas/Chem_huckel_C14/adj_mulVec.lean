/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma adj_mulVec (v : Fin 14 → ℂ) (x : Fin 14) :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).mulVec v x = v (x - 1) + v (x + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (by revert x; decide)]

/-- **Hückel theory for the C₁₄ ring.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₄`
if and only if `μ = 2 cos (2πk/14)` for some `k ∈ {0, …, 13}`. -/

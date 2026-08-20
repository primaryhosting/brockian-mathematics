import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

lemma adjMatrix_map :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℝ).map (Complex.ofRealHom) = A12 := by
  ext i j
  by_cases h : (SimpleGraph.cycleGraph 12).Adj i j <;>
    simp [A12, SimpleGraph.adjMatrix, h]

/-- The characteristic polynomial of the adjacency matrix of `C₁₂` factors with roots
`2 cos (2πk/12)`. -/

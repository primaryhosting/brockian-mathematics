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

theorem cycleGraph12_charpoly :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℝ).charpoly =
      ∏ k : Fin 12, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 12))) := by
  refine Polynomial.map_injective (Complex.ofRealHom) Complex.ofReal_injective ?_
  rw [← Matrix.charpoly_map, adjMatrix_map, A12_charpoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro k _
  simp

/-- **Hückel theory for C₁₂.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₂` are exactly the numbers `2 cos (2 π k / 12)`, `k = 0, …, 11`. -/

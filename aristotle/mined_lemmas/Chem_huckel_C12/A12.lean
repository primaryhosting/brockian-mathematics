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

noncomputable def A12 : Matrix (Fin 12) (Fin 12) ℂ := (SimpleGraph.cycleGraph 12).adjMatrix ℂ

/-- The matrix of characters (a Vandermonde matrix in the powers of `ω`). -/

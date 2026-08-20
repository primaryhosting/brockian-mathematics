import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₂`

We show that the eigenvalues (i.e. the spectrum) of the adjacency matrix of the cycle graph
`C₁₂`, viewed as a complex matrix indexed by `ZMod 12`, are exactly the numbers
`2 * cos (2 * π * k / 12)` for `k = 0, …, 11`.

The proof goes through the cyclic shift matrix `S` on `ZMod 12`: the adjacency matrix is
`S + S ^ 11`, the spectrum of `S` is the set of `12`-th roots of unity, and the polynomial
spectral mapping theorem over `ℂ` transports this to the adjacency matrix.
-/

namespace Chem

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod 12`. -/

lemma C12adj_eq_adjMatrix : C12adj = (SimpleGraph.cycleGraph 12).adjMatrix ℂ := by
  ext i j
  simp only [C12adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  have h : ((SimpleGraph.cycleGraph 12).Adj i j) ↔ (j = i + 1 ∨ j = i - 1) := by
    revert i j; decide
  simp [h]


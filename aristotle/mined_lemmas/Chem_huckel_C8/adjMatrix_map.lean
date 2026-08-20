/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₈` (the Hückel π-system of cyclooctatetraene)
are `2 cos (2πk/8)` for `k = 0, …, 7`.  This is expressed as a complete factorisation of the
characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 8`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix built from the
primitive eighth root of unity `ω = (√2/2)(1 + i)`.
-/

open Matrix Complex Polynomial SimpleGraph

namespace Chem

/-- The primitive eighth root of unity `exp (2πi/8) = (√2/2)(1 + i)`. -/

lemma adjMatrix_map :
    ((cycleGraph 8).adjMatrix ℝ).map (algebraMap ℝ ℂ) = (cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  split <;> simp

/-- **Hückel theory for cyclic C₈ (cyclooctatetraene).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₈` is
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`; equivalently, the adjacency eigenvalues of `C₈` are exactly
`2 cos (2πk/8)` for `k = 0, …, 7`, counted with multiplicity. -/

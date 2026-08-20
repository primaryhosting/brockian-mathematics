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

lemma adj_mul_dft : ((cycleGraph 8).adjMatrix ℂ) * dft = dft * eigDiag := by
  ext j l
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_eight, dft, eigDiag, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply] <;>
    norm_num +decide <;>
    ring_nf <;>
    norm_num [om_shift, om_sq, om3, om4, om5, om6, om7] <;>
    try ring


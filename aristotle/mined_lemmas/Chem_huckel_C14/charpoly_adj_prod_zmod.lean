/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/

theorem charpoly_adj_prod_zmod :
    adjC14.charpoly = ∏ k : ZMod 14, (X - C ((2 * Real.cos (theta k.val) : ℝ) : ℂ)) := by
  rw [adj_conj, Matrix.charpoly_units_conj]
  exact Matrix.charpoly_diagonal _

/-- **Hückel theory for the cycle `C₁₄`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₄` factors as `∏_{k=0}^{13} (X - 2 cos (2πk/14))`; i.e. the
adjacency eigenvalues of `C₁₄` are exactly the numbers `2 cos (2πk/14)`, `k = 0, …, 13`
(listed with multiplicity). -/

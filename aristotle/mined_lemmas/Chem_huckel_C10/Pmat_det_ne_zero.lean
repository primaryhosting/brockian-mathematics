/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- **Hückel theory for the C₁₀ cycle.**  The adjacency spectrum of the cycle graph `C₁₀`
consists exactly of the numbers `2 cos (2πk/10)`, `k = 0, …, 9`, and the characteristic
polynomial factors accordingly (so these are the eigenvalues with multiplicity). -/

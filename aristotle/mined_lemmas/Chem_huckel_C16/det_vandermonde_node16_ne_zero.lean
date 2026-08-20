/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma det_vandermonde_node16_ne_zero : (Matrix.vandermonde node16).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (isPrimitiveRoot_zeta16.pow_inj a.isLt b.isLt hab)

/-- **Hückel theory for cyclic C₁₆.**  The adjacency matrix of the cycle graph `C₁₆` is
diagonalized by the discrete Fourier (Vandermonde) matrix, and its eigenvalues are exactly
`2·cos(2πk/16)` for `k = 0, 1, …, 15` (with multiplicity). -/

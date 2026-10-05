/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as an ordinary block comment with identical text.)

import Mathlib

/-!
# Huckel C 11

The adjacency eigenvalues of the cycle graph `C₁₁` are `2·cos(2πk/11)` for `k = 0, …, 10`.

The proof diagonalizes the adjacency matrix `A` of `SimpleGraph.cycleGraph 11` by the
discrete Fourier (Vandermonde) matrix `U j k = ω^{jk}`, where `ω = exp(2πi/11)`:
`A * U = U * diagonal d` with `d k = ω^k + ω^{-k} = 2 cos (2πk/11)`.
Since `det U ≠ 0` (`Matrix.det_vandermonde_ne_zero_iff`, `ω` being a primitive root),
`det (A - z) = ∏ k (d k - z)`, and `Matrix.exists_mulVec_eq_zero_iff` converts this into
the statement about eigenvalues.
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 11-th root of unity. -/

theorem UC11_det_ne_zero : UC11.det ≠ 0 := by
  rw [UC11]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  exact Fin.ext (om_isPrimitiveRoot.pow_inj a.isLt b.isLt hab)


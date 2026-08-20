import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to be the very first command of a file, so the header comment above
is placed immediately after the import.)

## Contents

The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₆` is `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₆`.  We show that the characteristic polynomial of `A`
factors as `∏_{k=0}^{15} (X - 2 cos (2 π k / 16))`, i.e. that the adjacency eigenvalues of `C₁₆`,
listed with multiplicity, are exactly `2 cos (2 π k / 16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix built from
the standard additive character `ZMod.stdAddChar` of `ZMod 16`; the orthogonality relation used is
`AddChar.sum_mulShift`, and the invariance of the characteristic polynomial under conjugation comes
from `Matrix.charpoly_mul_comm`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial Complex SimpleGraph

/-- The additive character `x ↦ exp (2 π I x / 16)` on `ZMod 16`. -/

theorem huckel_C16_eigenvector (k : ZMod 16) :
    (fun j : ZMod 16 => ec (j * k)) ≠ 0 ∧
      ((cycleGraph 16).adjMatrix ℂ).mulVec (fun j : ZMod 16 => ec (j * k)) =
        (2 * Real.cos (2 * Real.pi * k.val / 16) : ℂ) • fun j : ZMod 16 => ec (j * k) := by
  constructor
  · intro h
    have h0 : ec ((0 : ZMod 16) * k) = 0 := congrFun h 0
    rw [zero_mul, ec.map_zero_eq_one] at h0
    exact one_ne_zero h0
  · funext i
    have h := congrFun (congrFun A16_mul_U16 i) k
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simpa [Matrix.mulVec, dotProduct, U16, lam, A16, mul_comm] using h

end Chem


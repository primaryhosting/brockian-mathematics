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

theorem huckel_C16 :
    ((cycleGraph 16).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 16, (X - C (2 * Real.cos (2 * Real.pi * k / 16) : ℂ)) := by
  have h : ((cycleGraph 16).adjMatrix ℂ).charpoly = A16.charpoly := rfl
  rw [h, A16_charpoly]
  rw [show (∏ k : ZMod 16, (X - C (lam k)))
      = ∏ k : Fin 16, (X - C (2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ)) from rfl,
    Fin.prod_univ_eq_prod_range
      (fun m => X - C (2 * Real.cos (2 * Real.pi * (m : ℝ) / 16) : ℂ)) 16]

/-- For each `k`, the discrete Fourier mode `j ↦ exp (2 π I j k / 16)` is a nonzero eigenvector
of the adjacency matrix of `C₁₆` with eigenvalue `2 cos (2 π k / 16)`. -/

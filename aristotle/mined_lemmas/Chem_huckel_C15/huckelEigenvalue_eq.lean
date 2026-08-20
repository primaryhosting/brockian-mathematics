/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15

Category: Chemistry.  Target: `Chem.huckel_C15`.

The Hückel (adjacency) eigenvalues of the cycle graph `C₁₅` are `2 cos (2πk/15)`, `k = 0, …, 14`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i k = ζ ^ (k * i)` with `ζ = exp (2πi/15)`, and then uses
`spectrum.units_conjugate` together with `spectrum_diagonal`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

theorem huckelEigenvalue_eq (k : Fin 15) :
    huckelEigenvalue k = zeta ^ (k.val) + (zeta ^ (k.val))⁻¹ := by
  have h1 : zeta ^ (k.val) = Complex.exp ((2 * Real.pi * k.val / 15 : ℝ) * I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [huckelEigenvalue, h1, two_cos_eq]
  push_cast
  ring_nf

/-! ### The eigenvectors -/


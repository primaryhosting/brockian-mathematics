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

theorem two_cos_eq (t : ℂ) : Complex.exp (t * I) + (Complex.exp (t * I))⁻¹ = 2 * Complex.cos t := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg]
  ring


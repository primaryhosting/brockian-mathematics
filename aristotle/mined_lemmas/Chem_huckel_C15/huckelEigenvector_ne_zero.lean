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

theorem huckelEigenvector_ne_zero (k : Fin 15) : huckelEigenvector k ≠ 0 := by
  intro h
  have h0 : huckelEigenvector k 0 = 0 := by rw [h]; rfl
  simp [huckelEigenvector] at h0

/-- For each `k`, the vector `i ↦ ζ ^ (k * i)` (with `ζ = exp (2πi/15)`) is a nonzero eigenvector
of the adjacency matrix of `C₁₅` with eigenvalue `2 cos (2πk/15)`. -/

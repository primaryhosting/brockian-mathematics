/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

noncomputable def cycleLaplacianZ : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if i = j then 2 else if i - j = 1 ∨ i - j = -1 then -1 else 0

/-- The discrete Fourier matrix, whose columns are the eigenvectors
`v k (j) = exp (2 π I k j / n)`. -/

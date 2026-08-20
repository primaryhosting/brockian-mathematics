import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix (indexed by
`ZMod n`) with diagonal entries `2` and `-1` on the two cyclic off-diagonals. -/

noncomputable def fourierUnit (n : ℕ) [NeZero n] : (Matrix (ZMod n) (ZMod n) ℂ)ˣ where
  val := fourierMatrix n
  inv := fourierMatrixInv n
  val_inv := fourierMatrix_mul_inv
  inv_val := fourierMatrixInv_mul

/-- The `k`-th eigenvalue is the real number `2 - 2 cos (2 π k / n)`. -/

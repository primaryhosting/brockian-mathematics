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

lemma cycleLaplacian_mul_fourierMatrix (hn : 3 ≤ n) :
    cycleLaplacian n * fourierMatrix n = fourierMatrix n * diagonal (cycleEigenvalue n) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal,
    cycleLaplacian_row_sum hn i (fun j => fourierMatrix n j k)]
  simp only [fourierMatrix, cycleEigenvalue]
  rw [show ((i + 1) * k) = i * k + k by ring, show ((i - 1) * k) = i * k + -k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring


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

lemma cycleLaplacian_row_sum (hn : 3 ≤ n) (i : ZMod n) (f : ZMod n → ℂ) :
    ∑ j : ZMod n, cycleLaplacian n i j * f j = 2 * f i - f (i + 1) - f (i - 1) := by
  simp [cycleLaplacian_apply hn, sub_mul, ite_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- The Fourier vectors diagonalise the cycle Laplacian. -/

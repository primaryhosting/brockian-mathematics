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

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

theorem spectrum_cycleLaplacian (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n)
      = {μ : ℂ | ∃ k ∈ Finset.range n,
          μ = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)} := by
  rw [← cycle_laplacian_spectrum n hn]
  ext μ
  exact mem_spectrum_iff_exists_eigenvector _ μ

end Frontier.Spectral


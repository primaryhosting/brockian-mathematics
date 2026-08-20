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

theorem cycle_laplacian_eigenvalue_iff (n : ℕ) [NeZero n] (hn : 3 ≤ n) (mu : ℂ) :
    (∃ v : ZMod n → ℂ, v ≠ 0 ∧ cycleLaplacian n *ᵥ v = mu • v)
      ↔ ∃ k < n, mu = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  rw [mem_spectrum_iff_exists_eigenvector, cycle_laplacian_spectrum n hn]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk), rfl⟩

end Frontier.Spectral


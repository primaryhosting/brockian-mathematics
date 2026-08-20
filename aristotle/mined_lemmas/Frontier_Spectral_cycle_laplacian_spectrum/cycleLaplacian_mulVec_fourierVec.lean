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

lemma cycleLaplacian_mulVec_fourierVec (hn : 3 ≤ n) (k : ZMod n) :
    cycleLaplacian n *ᵥ (fun j => ZMod.stdAddChar (j * k))
      = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) •
          (fun j => ZMod.stdAddChar (j * k)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [cycleLaplacian_row_sum hn i (fun j => ZMod.stdAddChar (j * k)), ← cycleEigenvalue_eq,
    cycleEigenvalue, show ((i + 1) * k) = i * k + k by ring,
    show ((i - 1) * k) = i * k + -k by ring, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- Membership in the spectrum of a matrix is having an eigenvector. -/

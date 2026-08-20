/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

theorem cycle_lapMatrix_eigenvector (N : ℕ) (k : ℤ) :
    (cycleGraph (N + 3)).lapMatrix ℝ *ᵥ cycleVec (N + 3) k
      = (2 - 2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ))) • cycleVec (N + 3) k := by
  funext v
  rw [lap_mulVec, cycleVec_lap]
  rfl

/-! ## Main results -/

/-- The set of Laplacian eigenvalues of the cycle graph `C n` admitting an eigenvector
whose entries sum to zero, i.e. an eigenvector orthogonal to the all-ones vector. -/

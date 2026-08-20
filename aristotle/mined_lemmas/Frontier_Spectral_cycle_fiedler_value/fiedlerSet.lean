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

def fiedlerSet (n : ℕ) : Set ℝ :=
  {mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ j, x j) = 0 ∧
    (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x}

/-- **The Fiedler value (algebraic connectivity) of the cycle graph `C n` for `n ≥ 3`.**
The smallest Laplacian eigenvalue of `C n` admitting an eigenvector orthogonal to the
all-ones vector (i.e. the second-smallest Laplacian eigenvalue) equals `2 - 2 cos (2 π / n)`. -/

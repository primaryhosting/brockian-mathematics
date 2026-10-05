import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

def onsagerLogZ (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (8 * Real.pi ^ 2)) *
    ∫ x in (0 : ℝ)..(2 * Real.pi), ∫ y in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos x + Real.cos y))

/-- The partition function of the periodic 1D Ising chain (ring) with `k + 1` sites. -/

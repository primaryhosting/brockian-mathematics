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

def tw (K : ℝ) (a b : Bool) : ℝ := Real.exp (K * spinVal a * spinVal b)

/-- Entries of the `k`-th power of the `2 × 2` transfer matrix. -/

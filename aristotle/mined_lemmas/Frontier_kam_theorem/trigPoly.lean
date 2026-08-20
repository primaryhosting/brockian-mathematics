/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The character `x ↦ e^{2πi k x}` on the circle `ℝ / ℤ`. -/

noncomputable def trigPoly (s : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, c k * torusChar k x

/-- The formal solution of the homological (small–divisor) equation
`u (x + ω) - u x = f x` for `f = trigPoly s c`. -/

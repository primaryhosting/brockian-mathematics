/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires `import`
-- commands to precede every module docstring; the text is otherwise verbatim.)

import Mathlib

open Real Filter MeasureTheory Set

namespace Zeta23Scaffold

/-- For `x > 0`, the function `t ↦ t * exp (-(t * x))` is integrable on `(0, ∞)` and its
integral there equals `1 / x ^ 2`. -/

theorem integral_sinc_sq' : ∫ x : ℝ, (Real.sinc x) ^ 2 = π := by
  rw [← integral_sinc_sq]
  apply integral_congr_ae
  have h0 : ∀ᵐ (x : ℝ), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


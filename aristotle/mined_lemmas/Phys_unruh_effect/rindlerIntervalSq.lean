/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

noncomputable def rindlerIntervalSq (a c τ₁ τ₂ : ℝ) : ℝ :=
  (c * (rindlerT a c τ₁ - rindlerT a c τ₂)) ^ 2 - (rindlerX a c τ₁ - rindlerX a c τ₂) ^ 2

/-- The analytic continuation of the worldline interval to complex proper-time separation.
Vacuum two-point (Wightman) functions along the worldline are functions of this quantity, so
its periodicity in imaginary time is exactly the KMS thermality condition. -/

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

lemma deriv2_rindlerT (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (deriv (rindlerT a c)) = fun τ => (a / c) * Real.sinh (a * τ / c) := by
  rw [deriv_rindlerT a c ha hc]
  funext τ
  have h2 := (Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_lin a c τ)
  exact (h2.congr_deriv (by ring)).deriv


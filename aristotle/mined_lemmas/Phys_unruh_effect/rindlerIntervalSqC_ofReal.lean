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

theorem rindlerIntervalSqC_ofReal (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ₁ τ₂ : ℝ) :
    rindlerIntervalSqC a c ((τ₁ - τ₂ : ℝ) : ℂ) = ((rindlerIntervalSq a c τ₁ τ₂ : ℝ) : ℂ) := by
  rw [rindler_intervalSq_eq a c ha hc]
  simp only [rindlerIntervalSqC]
  have harg : ((a : ℂ)) * ((τ₁ - τ₂ : ℝ) : ℂ) / (2 * (c : ℂ))
      = ((a * (τ₁ - τ₂) / (2 * c) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_sinh]
  push_cast
  ring

/-! ## KMS periodicity in imaginary proper time -/

/-- The complexified worldline correlation variable is periodic in imaginary proper time with
period `2πc/a`. This is the KMS condition at inverse temperature `β = 2πc/a`. -/

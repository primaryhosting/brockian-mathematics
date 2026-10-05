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

theorem rindlerIntervalSqC_kms_period (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (Δ : ℂ) :
    rindlerIntervalSqC a c (Δ + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ))
      = rindlerIntervalSqC a c Δ := by
  simp only [rindlerIntervalSqC]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have harg : (a : ℂ) * (Δ + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ)) / (2 * (c : ℂ))
      = (a : ℂ) * Δ / (2 * (c : ℂ)) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_add]
  have h1 : Complex.sinh ((Real.pi : ℂ) * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]
    simp
  have h2 : Complex.cosh ((Real.pi : ℂ) * Complex.I) = -1 := by
    rw [Complex.cosh_mul_I]
    simp
  rw [h1, h2]
  ring

/-- Minimality: `2πc/a` is the smallest positive imaginary period, so the KMS temperature is
uniquely determined. -/

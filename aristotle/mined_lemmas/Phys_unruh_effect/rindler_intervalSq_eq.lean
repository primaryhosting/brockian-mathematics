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

theorem rindler_intervalSq_eq (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ₁ τ₂ : ℝ) :
    rindlerIntervalSq a c τ₁ τ₂
      = 4 * (c ^ 2 / a) ^ 2 * Real.sinh (a * (τ₁ - τ₂) / (2 * c)) ^ 2 := by
  have hkey : Real.cosh (a * τ₁ / c - a * τ₂ / c) - 1
      = 2 * Real.sinh (a * (τ₁ - τ₂) / (2 * c)) ^ 2 := by
    have h := cosh_sub_one (a * τ₁ / c - a * τ₂ / c)
    have harg : (a * τ₁ / c - a * τ₂ / c) / 2 = a * (τ₁ - τ₂) / (2 * c) := by
      field_simp
    rw [harg] at h
    exact h
  rw [Real.cosh_sub] at hkey
  have h1 := Real.cosh_sq_sub_sinh_sq (a * τ₁ / c)
  have h2 := Real.cosh_sq_sub_sinh_sq (a * τ₂ / c)
  simp only [rindlerIntervalSq, rindlerT, rindlerX]
  have hexp : (c * (c / a * Real.sinh (a * τ₁ / c) - c / a * Real.sinh (a * τ₂ / c))) ^ 2
      - (c ^ 2 / a * Real.cosh (a * τ₁ / c) - c ^ 2 / a * Real.cosh (a * τ₂ / c)) ^ 2
      = (c ^ 2 / a) ^ 2 *
        ((Real.sinh (a * τ₁ / c) - Real.sinh (a * τ₂ / c)) ^ 2
          - (Real.cosh (a * τ₁ / c) - Real.cosh (a * τ₂ / c)) ^ 2) := by
    field_simp
  rw [hexp]
  nlinarith [h1, h2, hkey]

/-- The complexified interval restricts to the real interval on real proper-time separations. -/

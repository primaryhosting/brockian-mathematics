import Mathlib
/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal BoundedContinuousFunction

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

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/

theorem integral_satoTate_density {α β : ℝ} (h : α ≤ β) :
    (∫ θ in Set.Icc α β, 2 / Real.pi * Real.sin θ ^ 2)
      = (Real.sin α * Real.cos α - Real.sin β * Real.cos β + β - α) / Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
    intervalIntegral.integral_const_mul, integral_sin_sq]
  have := Real.pi_pos
  field_simp


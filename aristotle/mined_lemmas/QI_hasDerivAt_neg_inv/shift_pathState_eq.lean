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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem shift_pathState_eq (ρ σ : Mat n) (s t : ℝ) :
    (σ + (t : ℂ) • 1) + (s : ℂ) • (ρ - σ) = pathState ρ σ s + (t : ℂ) • 1 := by
  rw [pathState]
  abel

section Derivative

open scoped Matrix.Norms.Operator

/-- The trace, as a continuous linear functional on matrices. -/

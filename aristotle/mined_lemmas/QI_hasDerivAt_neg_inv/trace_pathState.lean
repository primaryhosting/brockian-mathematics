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


theorem trace_pathState (ρ σ : Mat n) (s : ℝ) (A : Mat n) :
    (pathState ρ σ s * A).trace = (σ * A).trace + (s : ℂ) * ((ρ * A).trace - (σ * A).trace) := by
  rw [pathState, Matrix.add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul,
    Matrix.sub_mul, Matrix.trace_sub]
  simp

/-- Integrability of the integrand of the integral representation of `Tr (A log ω)`. -/

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


theorem relEntropy_eq_res_integral (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ = ∫ t in Ioi (0:ℝ), ((ρ * res σ t).trace.re - (ρ * res ρ t).trace.re) := by
  rw [relEntropy, trace_mul_logM_integral hρ ρ, trace_mul_logM_integral hσ ρ,
    ← MeasureTheory.integral_sub (integrableOn_logKernel_trace hρ ρ)
      (integrableOn_logKernel_trace hσ ρ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  ring

/-- The inner integral over `t`, at a fixed point of the path. -/

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


theorem hasDerivAt_trace_res_path (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ 1) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    HasDerivAt (fun u : ℝ => -(A * res (pathState ρ σ u) t).trace.re)
      ((A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) s := by
  have hR := hasDerivAt_res_path hρ hσ h0 h1 ht
  have hAR := hR.const_mul A
  have h2 := (((traceCLM n).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt s hAR
  have h3 := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt s h2
  have h4 := h3.neg
  convert h4 using 1
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', traceCLM_apply,
    Complex.reCLM_apply, mul_neg, Matrix.trace_neg, Complex.neg_re, neg_neg, mul_assoc]

/-- The fundamental theorem of calculus along the path. -/

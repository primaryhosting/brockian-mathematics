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


theorem integral_path_deriv (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    (∫ s in Ioo (0:ℝ) 1,
        (A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      = (A * res σ t).trace.re - (A * res ρ t).trace.re := by
  have hle : (0:ℝ) ≤ 1 := by norm_num
  have hderiv : ∀ s ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => -(A * res (pathState ρ σ u) t).trace.re)
        ((A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) s := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    exact hasDerivAt_trace_res_path hρ hσ hs.1 hs.2 ht A
  have hcont : ContinuousOn (fun s : ℝ =>
      (A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) (uIcc 0 1) := by
    rw [Set.uIcc_of_le hle]
    intro s hs
    have hAt := continuousAt_path_trace hρ hσ A (ρ - σ) (p := (t, s)) ht hs.1 hs.2
    exact (hAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at key
  rw [key, pathState_zero, pathState_one]
  ring

end Derivative

/-- The relative entropy as an integral of resolvent traces. -/

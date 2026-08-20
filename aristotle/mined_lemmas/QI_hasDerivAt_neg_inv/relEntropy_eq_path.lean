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


theorem relEntropy_eq_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace) :
    relEntropy ρ σ = ∫ s in Ioo (0:ℝ) 1, (1 - s) * bkm (pathState ρ σ s) (ρ - σ) := by
  rw [relEntropy_eq_res_integral hρ hσ,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => (integral_path_deriv hρ hσ (le_of_lt ht) ρ).symm),
    MeasureTheory.integral_integral_swap (integrable_uncurry_path hρ hσ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  exact integral_res_quad_path hρ hσ htr (le_of_lt hs.1) (le_of_lt hs.2)

/-- Integrability along the path. -/

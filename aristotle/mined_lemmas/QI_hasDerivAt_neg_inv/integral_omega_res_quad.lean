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


theorem integral_omega_res_quad (hω : ω.PosDef) (Δ : Mat n) :
    (∫ t in Ioi (0:ℝ), (ω * res ω t * Δ * res ω t).trace.re) = Δ.trace.re := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => trace_omega_res_quad_re hω (le_of_lt ht) Δ)]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
    (((integrableOn_resSq (eigV_pos hω i)).const_mul (eigV hω i)).const_mul _))]
  have hsum : ∀ i : Fin n,
      (∫ t in Ioi (0:ℝ), ((cj hω Δ) i i).re * (eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹)))
        = ((cj hω Δ) i i).re := by
    intro i
    rw [MeasureTheory.integral_const_mul, integral_resSq (eigV_pos hω i), mul_one]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsum i)]
  rw [← trace_cj hω Δ, Matrix.trace, Complex.re_sum]
  rfl


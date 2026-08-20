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


theorem integral_logKernel {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), ((1 + t)⁻¹ - (a + t)⁻¹) = Real.log a := by
  have hlim : Tendsto (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) atTop (𝓝 0) := by
    have hratio : Tendsto (fun t : ℝ => 1 + (1 - a) / (a + t)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => (1 - a) / (a + t)) atTop (𝓝 0) := by
        apply Filter.Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_left _ a tendsto_id
      simpa using h0.const_add 1
    have heq : ∀ᶠ t : ℝ in atTop, Real.log (1 + t) - Real.log (a + t)
        = Real.log (1 + (1 - a) / (a + t)) := by
      filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-a)] with t ht hta
      have h1 : (0:ℝ) < 1 + t := by linarith
      have h2 : (0:ℝ) < a + t := by linarith
      rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
      congr 1
      field_simp
      ring
    rw [tendsto_congr' heq]
    have := (Real.continuousAt_log (x := 1) one_ne_zero).tendsto.comp hratio
    simpa using this
  have hderiv : ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) ((1 + t)⁻¹ - (a + t)⁻¹) t := by
    intro t ht
    simp only [mem_Ioi] at ht
    have h1 : (1:ℝ) + t ≠ 0 := by positivity
    have h2 : a + t ≠ 0 := by positivity
    have d1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + t)⁻¹ t := by
      simpa using ((hasDerivAt_id t).const_add (1:ℝ)).log h1
    have d2 : HasDerivAt (fun t : ℝ => Real.log (a + t)) (a + t)⁻¹ t := by
      simpa using ((hasDerivAt_id t).const_add a).log h2
    exact d1.sub d2
  have hcont : ContinuousWithinAt (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    exact (ContinuousAt.log (by fun_prop) (by norm_num)).sub
      (ContinuousAt.log (by fun_prop) (by simpa using ha.ne'))
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_logKernel ha) hlim
  rw [h]
  simp

/-- The logarithmic mean is at most the arithmetic mean: `2/(a+b) ≤ ∫₀^∞ dt/((a+t)(b+t))`. -/

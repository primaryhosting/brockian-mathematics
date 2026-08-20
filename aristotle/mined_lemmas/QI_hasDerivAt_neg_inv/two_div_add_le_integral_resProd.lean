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


theorem two_div_add_le_integral_resProd {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 / (a + b) ≤ ∫ t in Ioi (0:ℝ), (a + t)⁻¹ * (b + t)⁻¹ := by
  set c := (a + b) / 2 with hcdef
  have hc : 0 < c := by positivity
  have hmono : ∫ t in Ioi (0:ℝ), (c + t)⁻¹ * (c + t)⁻¹
      ≤ ∫ t in Ioi (0:ℝ), (a + t)⁻¹ * (b + t)⁻¹ := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_resSq hc) (integrableOn_resProd ha hb)
      measurableSet_Ioi (fun t ht => ?_)
    simp only [mem_Ioi] at ht
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    rw [← mul_inv, ← mul_inv]
    apply inv_anti₀ (by positivity)
    rw [hcdef]
    nlinarith [sq_nonneg (a - b)]
  have hcinv : ∫ t in Ioi (0:ℝ), (c + t)⁻¹ * (c + t)⁻¹ = 1 / c := by
    have h := integral_resSq hc
    rw [MeasureTheory.integral_const_mul] at h
    field_simp at h ⊢
    linarith
  rw [hcinv] at hmono
  have heq : 2 / (a + b) = 1 / c := by rw [hcdef]; field_simp
  rw [heq]
  exact hmono


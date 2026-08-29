import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

open MeasureTheory Real Complex
open scoped FourierTransform

/-! ### The triangular (tent) function and its Fourier transform -/

/-- The tent function `t ↦ max (1 - |t|) 0`, real valued. -/

lemma integral_tentR_zero : ∫ v in (-1 : ℝ)..1, tentR v = 1 := by
  have h : ∫ v in (-1 : ℝ)..1, tentR v
      = (∫ v in (-1 : ℝ)..0, (1 + v)) + ∫ v in (0 : ℝ)..1, (1 - v) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (Continuous.intervalIntegrable continuous_tentR _ _)
      (Continuous.intervalIntegrable continuous_tentR _ _)]
    congr 1
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
      simp only [tentR, abs_of_nonpos hv.2]
      rw [max_eq_left (by linarith [hv.1])]
      ring
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      simp only [tentR, abs_of_nonneg hv.1]
      rw [max_eq_left (by linarith [hv.2])]
  rw [h, intervalIntegral.integral_add _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_sub _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
  norm_num [integral_id]


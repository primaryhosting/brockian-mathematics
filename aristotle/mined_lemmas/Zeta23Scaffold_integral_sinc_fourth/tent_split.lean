import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

open MeasureTheory Real FourierTransform Complex

namespace Zeta23Scaffold

/-! ## The tent function -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma tent_split (a : ℝ) :
    (∫ v in (-1:ℝ)..1, Complex.exp ((-(a:ℂ) * Complex.I) * v) * tentC v)
      = (∫ x in (-1:ℝ)..0, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x))
        + (∫ x in (0:ℝ)..1, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) - x)) := by
  have hcont : Continuous fun v : ℝ => Complex.exp ((-(a:ℂ) * Complex.I) * v) * tentC v :=
    (by fun_prop : Continuous fun v : ℝ =>
      Complex.exp ((-(a:ℂ) * Complex.I) * v)).mul continuous_tentC
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (-1:ℝ)) (b := 0) (c := 1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hx
    have h : tent x = 1 + x := by
      unfold tent
      rw [abs_of_nonpos hx.2]
      simp
      linarith [hx.1]
    simp [tentC, h]
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
    have h : tent x = 1 - x := by
      unfold tent
      rw [abs_of_nonneg hx.1]
      simp
      linarith [hx.2]
    simp [tentC, h]

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/

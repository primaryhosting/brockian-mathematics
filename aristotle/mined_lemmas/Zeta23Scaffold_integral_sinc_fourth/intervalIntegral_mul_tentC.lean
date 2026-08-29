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

namespace Zeta23Scaffold

open scoped FourierTransform
open MeasureTheory Real Complex

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1,1]`. -/

lemma intervalIntegral_mul_tentC (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ v in (-1 : ℝ)..1, g v * tentC v)
      = (∫ v in (-1 : ℝ)..0, g v * (1 + (v : ℂ))) + (∫ v in (0 : ℝ)..1, g v * (1 - (v : ℂ))) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (by apply Continuous.intervalIntegrable; exact hg.mul continuous_tentC)
      (by apply Continuous.intervalIntegrable; exact hg.mul continuous_tentC)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = -x := abs_of_nonpos hx.2
    simp only [tentC, tent, hax]
    rw [max_eq_left (by linarith)]
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = x := abs_of_nonneg hx.1
    simp only [tentC, tent, hax]
    rw [max_eq_left (by linarith)]
    push_cast
    ring


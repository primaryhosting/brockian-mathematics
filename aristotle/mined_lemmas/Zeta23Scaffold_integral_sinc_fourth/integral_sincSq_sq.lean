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

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_sincSq_sq : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have hL : ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ)
      = ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    have e1 : ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ)
        = ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [fourier_tentC_ae] with ξ hξ
      rw [hξ]
      push_cast
      ring
    rw [e1]
    exact _root_.integral_complex_ofReal
  have hR : ∫ x : ℝ, tentC x * tentC (-x) = ((∫ x : ℝ, tent x ^ 2 : ℝ) : ℂ) := by
    have e2 : ∫ x : ℝ, tentC x * tentC (-x) = ∫ x : ℝ, ((tent x ^ 2 : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [tentC, tent_neg]
      push_cast
      ring
    rw [e2]
    exact _root_.integral_complex_ofReal
  have h := integral_fourier_sq
  rw [hL, hR, integral_tent_sq] at h
  exact_mod_cast h


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

lemma integral_fourier_sq :
    ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ) = ∫ x : ℝ, tentC x * tentC (-x) := by
  rw [integral_fourier_mul integrable_tentC integrable_fourier_tentC]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fourier_fourier_eq continuous_tentC integrable_tentC integrable_fourier_tentC]

/-! ## The elementary integral `∫ tent² = 2/3` -/


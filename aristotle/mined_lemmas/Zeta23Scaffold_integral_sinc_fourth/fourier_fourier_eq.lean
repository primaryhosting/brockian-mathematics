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

lemma fourier_fourier_eq {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hFf : Integrable (𝓕 f)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have h := congrFun (hc.fourierInv_fourier_eq hf hFf) (-x)
  rwa [Real.fourierInv_eq_fourier_neg, neg_neg] at h


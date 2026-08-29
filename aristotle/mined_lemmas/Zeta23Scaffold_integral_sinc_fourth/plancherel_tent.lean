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

lemma plancherel_tent :
    ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ) = ∫ x : ℝ, (tentC x) * (tentC x) := by
  rw [multiplication_formula tentC (𝓕 tentC) integrable_tentC integrable_fourier_tentC]
  congr 1
  ext x
  congr 1
  have hinv : 𝓕⁻ (𝓕 tentC) (-x) = tentC (-x) :=
    integrable_tentC.fourierInv_fourier_eq integrable_fourier_tentC
      continuous_tentC.continuousAt
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  simpa [tentC_neg] using hinv

/-! ## The `L²` norm of the tent function -/


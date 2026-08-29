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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform Complex intervalIntegral

/-- The tent (triangle) function `max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma fourier_tent_eq_intervalIntegral (ξ : ℝ) :
    𝓕 tent ξ = ∫ v in (-1 : ℝ)..1, Complex.exp (-((2 * π * ξ * I) * v)) * tent v := by
  rw [Real.fourier_real_eq_integral_exp_smul, integral_eq_intervalIntegral_of_support]
  · apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [smul_eq_mul]
    congr 2
    push_cast
    ring
  · intro x hx
    rw [tent_eq_zero_of_one_le x hx, smul_zero]

/-- The basic antiderivative computation behind the Fourier transform of the tent function. -/

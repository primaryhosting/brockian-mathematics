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

lemma fourier_tent_interval (ξ : ℝ) :
    𝓕 tentC ξ = ∫ v in (-1:ℝ)..1,
      Complex.exp ((-((2 * π * ξ : ℝ) : ℂ) * Complex.I) * v) * tentC v := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    ext v
    congr 2
    push_cast
    ring
  · intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : (1:ℝ) ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tentC, tent_eq_zero h]


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

lemma tent_exp_integral (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (-(c * v)) * (1 + v))
      + (∫ v in (0 : ℝ)..1, Complex.exp (-(c * v)) * (1 - v))
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  have hv : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := fun v => Complex.ofRealCLM.hasDerivAt
  have hexp : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)))
      (Complex.exp (-(c * v)) * (-c)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => -(c * (v : ℂ))) (-c) v := by
      simpa using (((hv v).const_mul c).neg)
    exact h1.cexp
  have hF : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)) * (1 / c ^ 2 - (1 - v) / c))
      (Complex.exp (-(c * v)) * (1 - v)) v := by
    intro v
    have h4 : HasDerivAt (fun v : ℝ => (1 - (v : ℂ)) / c) (-(1 / c)) v := by
      simpa [div_eq_mul_inv] using ((((hv v).const_sub 1)).div_const c)
    have h3 : HasDerivAt (fun v : ℝ => (1 / c ^ 2 - (1 - (v : ℂ)) / c)) (-(-(1 / c))) v :=
      h4.const_sub (1 / c ^ 2)
    have h5 := (hexp v).mul h3
    convert h5 using 1
    field_simp
    ring
  have hG : ∀ v : ℝ,
      HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)) * (-(1 / c ^ 2) - (1 + v) / c))
      (Complex.exp (-(c * v)) * (1 + v)) v := by
    intro v
    have h4 : HasDerivAt (fun v : ℝ => (1 + (v : ℂ)) / c) (1 / c) v := by
      simpa [div_eq_mul_inv] using ((((hv v).const_add 1)).div_const c)
    have h3 : HasDerivAt (fun v : ℝ => (-(1 / c ^ 2) - (1 + (v : ℂ)) / c)) (-(1 / c)) v :=
      h4.const_sub (-(1 / c ^ 2))
    have h5 := (hexp v).mul h3
    convert h5 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hG v)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hF v)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  simp only [mul_zero, neg_zero, Complex.exp_zero, mul_neg, mul_one]
  field_simp
  ring

/-- The Fourier transform of the tent function is `sinc (π ξ)²`. -/

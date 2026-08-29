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

lemma integral_cexp_mul_one_sub (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (0 : ℝ)..1, Complex.exp (c * v) * (1 - (v : ℂ)))
      = Complex.exp c / c ^ 2 - (1 / c + 1 / c ^ 2) := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun x : ℝ => Complex.exp (c * x) * ((1 - (x : ℂ)) / c + 1 / c ^ 2))
      (Complex.exp (c * v) * (1 - (v : ℂ))) v := by
    intro v
    have h1 := hasDerivAt_cexp_mul c v
    have h2 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) / c + 1 / c ^ 2) (-1 / c) v := by
      have h3 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ))) (-1) v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_sub 1
      simpa [div_eq_mul_inv] using (h3.div_const c).add_const (1 / c ^ 2)
    have h4 := h1.mul h2
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => key v)]
  · simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      sub_self, zero_div, zero_add, sub_zero]
    field_simp
  · apply Continuous.intervalIntegrable
    fun_prop


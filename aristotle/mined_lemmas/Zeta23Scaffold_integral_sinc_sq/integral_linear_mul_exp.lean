/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and its Fourier transform -/

/-- The triangular ("tent") function `max (1 - |x|) 0`, supported on `[-1, 1]`. -/

lemma integral_linear_mul_exp (c A B : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, (A + B * (x : ℂ)) * Complex.exp (c * x)
      = (Complex.exp (c * b) * ((A + B * b) / c - B / c ^ 2))
        - (Complex.exp (c * a) * ((A + B * a) / c - B / c ^ 2)) := by
  have key : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) * ((A + B * t) / c - B / c ^ 2))
      ((A + B * (x : ℂ)) * Complex.exp (c * x)) x := by
    intro x
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * x) * c) x := by
      simpa using (h0.const_mul c).cexp
    have h2 : HasDerivAt (fun t : ℝ => (A + B * (t : ℂ)) / c - B / c ^ 2) (B / c) x := by
      simpa using (((h0.const_mul B).const_add A).div_const c).sub_const (B / c ^ 2)
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  exact Continuous.intervalIntegrable (by fun_prop) a b

/-- The Fourier integral of the tent function, reduced to an integral over `[-1, 1]`. -/

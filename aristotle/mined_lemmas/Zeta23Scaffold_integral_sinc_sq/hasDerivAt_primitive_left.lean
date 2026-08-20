import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

lemma hasDerivAt_primitive_left (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * t) * ((1 + (t : ℂ)) / c - 1 / c ^ 2))
      (Complex.exp (c * x) * (1 + (x : ℂ))) x := by
  have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  have he : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * x)) x := by
    simpa [mul_comm] using h1.cexp
  have h2 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)) / c - 1 / c ^ 2) (1 / c) x := by
    have h3 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ))) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add 1
    simpa using (h3.div_const c).sub_const (1 / c ^ 2)
  have h4 := he.mul h2
  convert h4 using 1
  field_simp; ring

/-- An antiderivative of `t ↦ exp (c t) (1 - t)`. -/

import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- Explicit antiderivative computation: the interval integral of a linear function times a
complex exponential. -/

theorem integral_lin_mul_cexp (a b : ℝ) (p q c : ℂ) (hc : c ≠ 0) :
    ∫ t in a..b, (p + q * (t : ℂ)) * Complex.exp (c * t) =
      (((p + q * b) / c - q / c ^ 2) * Complex.exp (c * b))
        - (((p + q * a) / c - q / c ^ 2) * Complex.exp (c * a)) := by
  have key : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => ((p + q * (t : ℂ)) / c - q / c ^ 2) * Complex.exp (c * t))
        ((p + q * (t : ℂ)) * Complex.exp (c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * t) * c) t := by
      simpa using (h1.const_mul c).cexp
    have h3 : HasDerivAt (fun t : ℝ => ((p + q * (t : ℂ)) / c - q / c ^ 2)) (q / c) t := by
      simpa using (((h1.const_mul q).const_add p).div_const c).sub_const (q / c ^ 2)
    have := h3.mul h2
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => key t)]
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The tent function on `[-1, 1]`, valued in `ℂ`. -/

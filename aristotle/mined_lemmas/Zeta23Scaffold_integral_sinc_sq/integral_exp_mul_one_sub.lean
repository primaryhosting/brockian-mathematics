/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory FourierTransform Complex intervalIntegral

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function.
Its Fourier transform is the squared sinc kernel. -/

lemma integral_exp_mul_one_sub (b : ℂ) (hb : b ≠ 0) :
    (∫ v in (0 : ℝ)..1, Complex.exp (b * v) * (1 - v)) =
      Complex.exp b / b ^ 2 - 1 / b - 1 / b ^ 2 := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun v : ℝ => Complex.exp (b * v) * ((1 + 1 / b) / b + (-1 / b) * v))
      (Complex.exp (b * v) * (1 - v)) v := by
    intro v
    have h := hasDerivAt_exp_linear b ((1 + 1 / b) / b) (-1 / b) v
    convert h using 1
    field_simp
    ring
  have hcont : IntervalIntegrable (fun v : ℝ => Complex.exp (b * v) * (1 - v)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => key v) hcont]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one, Complex.exp_zero]
  field_simp
  ring


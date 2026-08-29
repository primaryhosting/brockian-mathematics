import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped FourierTransform

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-! ## The tent function and its Fourier transform

The proof of `∫ (sin x / x) ^ 2 dx = π` goes through Fourier inversion applied to the
tent (triangle) function `x ↦ max 0 (1 - |x|)`, whose Fourier transform is
`w ↦ (sin (π w) / (π w)) ^ 2`. -/

/-- The triangle (tent) function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integral_expmul (z A B : ℂ) (a b : ℝ) :
    (∫ x in a..b, Complex.exp (z * x) * ((z * A + B) + z * B * x)) =
      Complex.exp (z * b) * (A + B * b) - Complex.exp (z * a) * (A + B * a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_expmul z A B x)
  apply Continuous.intervalIntegrable
  fun_prop


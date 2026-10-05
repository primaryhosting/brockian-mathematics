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

lemma hasDerivAt_exp_linear (b A B : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (b * v) * (A + B * v))
      (b * Complex.exp (b * v) * (A + B * v) + Complex.exp (b * v) * B) v := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun v : ℝ => Complex.exp (b * v)) (b * Complex.exp (b * v)) v := by
    simpa [mul_comm] using (h1.const_mul b).cexp
  have h3 : HasDerivAt (fun v : ℝ => A + B * v) B v := by
    simpa using (h1.const_mul B).const_add A
  simpa using h2.mul h3


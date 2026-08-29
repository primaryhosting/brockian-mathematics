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

The normalization integral of the sine kernel,
`∫ x : ℝ, (sin x / x) ^ 2 = π`.

The proof computes the Fourier transform of the triangle function
`tri x = max (1 - |x|) 0`, which is `w ↦ sinc (π w) ^ 2`, and then applies the
Fourier inversion formula at `0`.

Note that in Lean `sin 0 / 0 = 0`, so the integrand of the main statement differs from the
continuous extension `sinc` only on the null set `{0}`; the value of the integral is unaffected.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function on `ℝ`. -/

private lemma hasDerivAt_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (c * Complex.exp (c * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => c * (x:ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  simpa [mul_comm] using h1.cexp


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

lemma hasDerivAt_expmul (z A B : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * t) * (A + B * t))
      (Complex.exp (z * x) * ((z * A + B) + z * B * x)) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ)) (z * 1) x := hx.const_mul z
  have h2 := (h1.cexp).mul ((hx.const_mul B).const_add A)
  convert h2 using 1
  ring


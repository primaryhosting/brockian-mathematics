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

lemma integral_tri_exp (c : ℂ) (hc : c ≠ 0) :
    ∫ v : ℝ, Complex.exp (c * v) * tri v
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  rw [integral_tri_exp_split c, integral_tri_exp_left c hc, integral_tri_exp_right c hc]
  field_simp
  ring

/-- The Fourier transform of the tent function is `(sin (π w) / (π w))²`, for `w ≠ 0`. -/

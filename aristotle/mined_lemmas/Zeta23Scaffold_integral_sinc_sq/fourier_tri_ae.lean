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

lemma fourier_tri_ae :
    𝓕 tri =ᵐ[volume] fun w : ℝ => (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with w hw
  exact fourier_tri_of_ne_zero hw


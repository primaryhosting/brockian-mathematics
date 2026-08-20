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

The Dirichlet-type integral `∫_ℝ (sin x / x)^2 dx = π`.

The proof goes through the Fourier inversion formula applied to the triangle function
`tri ξ = max (1 - |ξ|) 0`, whose Fourier transform is `x ↦ sinc (π x)^2`.
-/

open MeasureTheory Real intervalIntegral
open scoped FourierTransform RealInnerProductSpace

namespace Zeta23Scaffold

/-- The triangle function `ξ ↦ max (1 - |ξ|) 0`, viewed as a complex-valued function. -/

lemma fourier_tri_eq_integral (x : ℝ) :
    𝓕 tri x = ∫ v : ℝ, Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I * v) * tri v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1 with v
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The key arithmetic identity behind the Fourier transform of the triangle function. -/

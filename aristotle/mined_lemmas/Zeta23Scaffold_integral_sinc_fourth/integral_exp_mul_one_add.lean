/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated as a plain comment on the first line of this file, since Lean 4
requires `import` commands to precede any module docstring.

## Method

With `T u = max 0 (1 - |u|)` the tent function, an explicit computation gives
`𝓕 T ξ = sinc (π ξ) ^ 2`.  The convolution theorem then yields `𝓕 (T ⋆ T) ξ = sinc (π ξ) ^ 4`,
and Fourier inversion at `0` gives
`∫ sinc (π ξ) ^ 4 dξ = (T ⋆ T) 0 = ∫ T ² = 2/3`.
Rescaling by `π` produces `∫ (sin x / x) ^ 4 dx = 2π/3`.
-/

open MeasureTheory Convolution FourierTransform
open scoped Real

namespace Zeta23Scaffold

/-- The tent (triangle) function `u ↦ max 0 (1 - |u|)`. -/

lemma integral_exp_mul_one_add (c : ℂ) (hc : c ≠ 0) :
    (∫ u in (-1:ℝ)..0, Complex.exp (c * u) * (1 + (u : ℂ)))
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have key : ∀ u : ℝ, HasDerivAt
      (fun t : ℝ => Complex.exp (c * t) * ((1 / c) * (t : ℂ) + (1 - 1 / c) / c))
      (Complex.exp (c * u) * (1 + (u : ℂ))) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul c
    have h3 : HasDerivAt (fun t : ℝ => (1 / c) * (t : ℂ) + (1 - 1 / c) / c) (1 / c) u := by
      simpa using
        ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (1 / c)).add_const ((1 - 1 / c) / c)
    have := h1.cexp.mul h3
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring


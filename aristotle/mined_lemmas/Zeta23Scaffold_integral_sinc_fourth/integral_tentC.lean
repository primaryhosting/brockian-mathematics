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

lemma integral_tentC : ∫ v : ℝ, tentC v = 1 := by
  have h := integral_exp_mul_tentC_split 0
  simp only [zero_mul, Complex.exp_zero, one_mul] at h
  rw [h]
  have d1 : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) + (t : ℂ) ^ 2 / 2) (1 + (u : ℂ)) u := by
    intro u
    have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have := hd.add ((hd.pow 2).div_const 2)
    convert this using 1
    simp
  have d2 : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) - (t : ℂ) ^ 2 / 2) (1 - (u : ℂ)) u := by
    intro u
    have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have := hd.sub ((hd.pow 2).div_const 2)
    convert this using 1
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d1 x)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d2 x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  ring

/-- Fourier transform of the tent function: `𝓕 tent ξ = sinc (π ξ) ^ 2`. -/

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

theorem integral_sinc_pi_fourth : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have hFint : Integrable (𝓕 gg) := by
    have : (𝓕 gg) = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := funext fourier_gg
    rw [this]
    exact sinc_pi_fourth_integrable.ofReal
  have hinv : 𝓕⁻ (𝓕 gg) 0 = gg 0 :=
    gg_integrable.fourierInv_fourier_eq hFint gg_continuous.continuousAt
  have hL : 𝓕⁻ (𝓕 gg) 0 = ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    rw [Real.fourierInv_eq]
    simp only [inner_zero_right, fourier_gg]
    simp
  rw [hL, gg_zero, integral_complex_ofReal] at hinv
  have := congrArg Complex.re hinv
  simpa using this

/-- `∫_ℝ (sin x / x)^4 dx = 2π/3`. -/

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

lemma gg_zero : gg 0 = ((2 : ℂ) / 3) := by
  rw [gg, convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (tentC t) (tentC (0 - t))
      = ((tent t ^ 2 : ℝ) : ℂ) := by
    intro t
    simp only [ContinuousLinearMap.mul_apply', zero_sub, tentC, tent_neg]
    push_cast
    ring
  simp only [this]
  rw [integral_complex_ofReal, integral_tent_sq]
  norm_num

/-- Pointwise bound `|sinc t| ^ 4 ≤ 2 / (1 + t²)`. -/

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

lemma tent_sq_eq_zero_of_mem_compl {x : ℝ} (hx : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    tent x ^ 2 = 0 := by
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
  have : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tent_eq_zero this]

/-- The `L²` norm of the tent function: `∫ tent² = 2/3`. -/

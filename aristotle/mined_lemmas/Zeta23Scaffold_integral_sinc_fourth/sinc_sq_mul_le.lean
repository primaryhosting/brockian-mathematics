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
-/

open MeasureTheory Complex intervalIntegral
open scoped FourierTransform Real

namespace Zeta23Scaffold

/-! ## Overview

We prove `∫ x : ℝ, (sin x / x) ^ 4 = 2 π / 3`.

The strategy is the Fourier multiplication formula `∫ 𝓕 f · g = ∫ f · 𝓕 g`.
Let `T` be the tent function `T x = max (1 - π |x|) 0`, supported in `[-1/π, 1/π]`.
An explicit computation gives `𝓕 T ξ = sinc(ξ)^2 / π =: S ξ`, and Fourier inversion
gives `𝓕 S = T` (both `T` and `S` are integrable, `T` is continuous, and `S` is even).
Hence `∫ S^2 = ∫ 𝓕 T · S = ∫ T · 𝓕 S = ∫ T^2 = 2/(3π)`, and since
`S^2 = sinc^4 / π^2` we get `∫ sinc^4 = 2π/3`.
-/

/-- The "tent" function `x ↦ max (1 - π|x|) 0`, supported on `[-1/π, 1/π]`. -/

theorem sinc_sq_mul_le (x : ℝ) : Real.sinc x ^ 2 * (1 + x ^ 2) ≤ 2 := by
  have h1 : Real.sinc x ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
  have h2 : x ^ 2 * Real.sinc x ^ 2 = Real.sin x ^ 2 := by
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · rw [Real.sinc_of_ne_zero h]; field_simp
  nlinarith [Real.sin_sq_le_one x]


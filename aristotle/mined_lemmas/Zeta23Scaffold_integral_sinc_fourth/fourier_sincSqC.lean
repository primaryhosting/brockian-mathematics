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

theorem fourier_sincSqC : 𝓕 sincSqC = tentC := by
  have h : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq integrable_tentC
      (by rw [fourier_tentC]; exact integrable_sincSqC)
  rw [fourier_tentC] at h
  funext x
  have h2 : 𝓕⁻ sincSqC (-x) = 𝓕 sincSqC x := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [← h2, h]
  simp [tentC, tent_neg]

/-! ### The multiplication formula -/


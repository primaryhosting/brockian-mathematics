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

noncomputable def antider (c A B : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-((c : ℂ) * t) * I) * ((I * A / c + B / (c : ℂ) ^ 2) + (I * B / c) * t)


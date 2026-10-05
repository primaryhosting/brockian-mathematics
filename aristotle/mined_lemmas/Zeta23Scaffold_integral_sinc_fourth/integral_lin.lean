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

theorem integral_lin (A B u v : ℝ) :
    ∫ x in u..v, (A + B * x) = (A * v + B * v ^ 2 / 2) - (A * u + B * u ^ 2 / 2) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have h : HasDerivAt (fun x : ℝ => A * x + B * x ^ 2 / 2) (A + B * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => A * x) A x := by
        simpa using (hasDerivAt_id x).const_mul A
      have h2 : HasDerivAt (fun x : ℝ => B * x ^ 2 / 2) (B * x) x := by
        have := (((hasDerivAt_pow 2 x).const_mul B).div_const 2)
        convert this using 1
        push_cast; ring
      simpa using h1.add h2
    convert h using 1
  · exact Continuous.intervalIntegrable (by fun_prop) _ _


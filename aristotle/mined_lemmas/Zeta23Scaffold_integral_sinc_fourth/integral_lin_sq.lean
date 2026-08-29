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

theorem integral_lin_sq (A B u v : ℝ) (hB : B ≠ 0) :
    ∫ x in u..v, (A + B * x) ^ 2 = (A + B * v) ^ 3 / (3 * B) - (A + B * u) ^ 3 / (3 * B) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => A + B * x) B x := by
      simpa using ((hasDerivAt_id x).const_mul B).const_add A
    have h := (h1.pow 3).div_const (3 * B)
    convert h using 1
    field_simp
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-! ### Elementary properties of the tent function -/


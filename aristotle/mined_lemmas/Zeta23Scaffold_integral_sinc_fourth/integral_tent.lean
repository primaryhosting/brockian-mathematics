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

theorem integral_tent : ∫ x : ℝ, tent x = 1 / π := by
  have hπ : 0 < π := Real.pi_pos
  have hcont : Continuous tent := continuous_tent
  rw [integral_eq_interval _ (by positivity : (0:ℝ) ≤ 1 / π) (fun x hx => tent_zero_of_le hx),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hle : -(1 / π) ≤ (0:ℝ) := neg_nonpos.mpr (by positivity)
  have h1 : ∫ x in (-(1 / π))..(0:ℝ), tent x = 1 / (2 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + π * x) (fun x hx => by
      rw [Set.uIcc_of_le hle] at hx
      exact tent_neg_part hx.2 hx.1), integral_lin]
    field_simp
    ring
  have h2 : ∫ x in (0:ℝ)..(1 / π), tent x = 1 / (2 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + (-π) * x) (fun x hx => by
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 1 / π)] at hx
      rw [tent_pos_part hx.1 hx.2]; ring), integral_lin]
    field_simp
    ring
  rw [h1, h2]
  field_simp
  ring


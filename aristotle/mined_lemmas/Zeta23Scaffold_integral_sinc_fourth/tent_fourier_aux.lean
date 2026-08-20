import Mathlib
/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The proof follows the classical Fourier-analytic route.  Writing `Λ` for the tent function
`Λ x = max (1 - |x|) 0`, an elementary computation gives `𝓕 Λ ξ = (sin (π ξ) / (π ξ))²`.
Fourier inversion then gives `𝓕 ((sin (π ·) / (π ·))²) = Λ`, and the multiplication formula
`∫ 𝓕 f · g = ∫ f · 𝓕 g` yields
`∫ (sin (π ξ) / (π ξ))⁴ dξ = ∫ Λ² = 2/3`.
Rescaling `x = π ξ` produces `∫ (sin x / x)⁴ dx = 2 π / 3`.
-/

open MeasureTheory Real Complex intervalIntegral
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and the squared sinc -/

/-- The tent (triangle) function `x ↦ max (1 - |x|) 0`. -/

lemma tent_fourier_aux (c : ℂ) (hc : c ≠ 0) :
    ∫ v : ℝ, Complex.exp (c * v) * tentC v
      = (Complex.exp c + Complex.exp (-c) - 2)/c^2 := by
  have hcont : Continuous (fun v : ℝ => Complex.exp (c * v) * tentC v) := by
    have := tentC_continuous; fun_prop
  have e1 : ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * tentC x
      = ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * (1 + (x : ℂ)) :=
    intervalIntegral.integral_congr
      (fun x hx => by simp only [tentC, tent_neg_side hx]; push_cast; ring)
  have e2 : ∫ x in (0:ℝ)..1, Complex.exp (c * x) * tentC x
      = ∫ x in (0:ℝ)..1, Complex.exp (c * x) * (1 - (x : ℂ)) :=
    intervalIntegral.integral_congr
      (fun x hx => by simp only [tentC, tent_pos_side hx]; push_cast; ring)
  have e3 : ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * (1 + (x : ℂ))
      = Complex.exp (c * (0:ℝ)) * ((1 + ((0:ℝ) : ℂ))/c - 1/c^2)
        - Complex.exp (c * ((-1:ℝ) : ℂ)) * ((1 + ((-1:ℝ) : ℂ))/c - 1/c^2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_G c hc v)
      (by apply Continuous.intervalIntegrable; fun_prop)
  have e4 : ∫ x in (0:ℝ)..1, Complex.exp (c * x) * (1 - (x : ℂ))
      = Complex.exp (c * ((1:ℝ) : ℂ)) * ((1 - ((1:ℝ) : ℂ))/c + 1/c^2)
        - Complex.exp (c * ((0:ℝ) : ℂ)) * ((1 - ((0:ℝ) : ℂ))/c + 1/c^2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_F c hc v)
      (by apply Continuous.intervalIntegrable; fun_prop)
  rw [integral_eq_interval _ (fun x hx => by simp [tentC, tent_eq_zero hx]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), e1, e2, e3, e4]
  push_cast
  simp only [Complex.exp_zero, mul_zero, mul_one]
  field_simp
  ring

/-- The Fourier transform of the tent function is the squared normalized sinc. -/

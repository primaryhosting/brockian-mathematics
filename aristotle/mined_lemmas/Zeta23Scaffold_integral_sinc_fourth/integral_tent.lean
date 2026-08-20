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

lemma integral_tent : ∫ x : ℝ, tent x = 1 := by
  have e1 : ∫ x in (-1:ℝ)..0, tent x = ∫ x in (-1:ℝ)..0, (1 + x) :=
    intervalIntegral.integral_congr (fun x hx => tent_neg_side hx)
  have e2 : ∫ x in (0:ℝ)..1, tent x = ∫ x in (0:ℝ)..1, (1 - x) :=
    intervalIntegral.integral_congr (fun x hx => tent_pos_side hx)
  rw [integral_eq_interval _ (fun x hx => tent_eq_zero hx),
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
        (tent_continuous.intervalIntegrable _ _) (tent_continuous.intervalIntegrable _ _),
      e1, e2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x + x^2/2)
        (fun x _ => by simpa using ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)))
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x - x^2/2)
        (fun x _ => by simpa using ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const 2)))
        (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num


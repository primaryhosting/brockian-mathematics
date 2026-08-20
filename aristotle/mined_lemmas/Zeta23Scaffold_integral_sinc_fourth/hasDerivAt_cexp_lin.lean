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

lemma hasDerivAt_cexp_lin (c : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (c * v)) (c * Complex.exp (c * v)) v := by
  have hofr : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := v))
  have h1 : HasDerivAt (fun v : ℝ => (c * (v : ℂ))) c v := by simpa using hofr.const_mul c
  simpa [mul_comm] using h1.cexp


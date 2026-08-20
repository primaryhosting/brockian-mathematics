import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Filter intervalIntegral
open scoped FourierTransform Topology Real

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integral_fourier_tri : ∫ ξ : ℝ, 𝓕 tri ξ = 1 := by
  have h := integrable_tri.fourierInv_fourier_eq integrable_fourier_tri
    (v := (0:ℝ)) continuous_tri.continuousAt
  rw [Real.fourierInv_eq'] at h
  simpa [tri_zero] using h

/-- **The normalization integral of the sine kernel**:
`∫_ℝ (sin x / x)² dx = π`.  (At `x = 0` the integrand is `0/0 = 0` in Lean, which does not
affect the value of the integral, since the integrand agrees almost everywhere with the
continuous function `sinc²`.) -/

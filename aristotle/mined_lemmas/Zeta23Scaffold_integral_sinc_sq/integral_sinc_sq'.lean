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

theorem integral_sinc_sq' : ∫ x : ℝ, (Real.sinc x) ^ 2 = π := by
  rw [← integral_congr_ae sinSq_div_sq_ae_eq_sincSq]
  exact integral_sinc_sq

/-- Normalized form of the sine-kernel normalization integral:
`∫_ℝ S(u)² du = 1` for `S(u) = sin (π u) / (π u)`. -/

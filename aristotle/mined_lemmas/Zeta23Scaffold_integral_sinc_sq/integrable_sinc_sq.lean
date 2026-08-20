import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

theorem integrable_sinc_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) :=
  (integrable_comp_mul_left_iff (fun x : ℝ => (Real.sin x / x) ^ 2) Real.pi_ne_zero).mp
    integrable_sinc_pi_sq

/-- **The normalization of the sine kernel**: `∫_ℝ (sin x / x)² dx = π`, as a Bochner integral
with respect to the Lebesgue measure `volume` on `ℝ`.

The integrand is understood pointwise as `(sin x / x)^2`; at `x = 0` this evaluates to `0` by the
junk-value convention for division, which does not affect the integral since `{0}` is null (the
integrand agrees a.e. with the continuous function `sinc x ^ 2`). -/

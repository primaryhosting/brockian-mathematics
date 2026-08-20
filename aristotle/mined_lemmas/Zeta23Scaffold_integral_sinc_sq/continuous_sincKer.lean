import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Real
open scoped Topology ENNReal

namespace Zeta23Scaffold

/-- The auxiliary kernel `t * sin x ^ 2 * exp (-(t * x))`, used to compute the integral of
`(sin x / x) ^ 2` by Tonelli's theorem, via `1 / x ^ 2 = ∫ t in (0, ∞), t * exp (-(t * x))`. -/

lemma continuous_sincKer : Continuous fun p : ℝ × ℝ => sincKer p.1 p.2 := by
  unfold sincKer
  fun_prop

/-! ### The `t`-integral: `∫_0^∞ t e^{-tx} dt = 1/x²` -/

/-- Antiderivative in `t` of `t * exp (-(t * x))`. -/

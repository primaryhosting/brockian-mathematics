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

lemma integrableOn_sincKer_t {x : ℝ} (hx : 0 < x) :
    IntegrableOn (sincKer x) (Ioi 0) := by
  have h : sincKer x = fun t : ℝ => Real.sin x ^ 2 * (t * Real.exp (-(t * x))) :=
    funext (sincKer_eq_mul x)
  rw [h]
  exact (integrableOn_t_mul_exp hx).const_mul _

/-! ### The `x`-integral: `∫_0^∞ t sin²x e^{-tx} dx = 2/(t²+4)` -/

/-- Antiderivative in `x` of `t * sin x ^ 2 * exp (-(t * x))`. -/

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

lemma nonneg_t_mul_exp {x : ℝ} : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t * Real.exp (-(t * x)) := fun _ ht =>
  mul_nonneg (le_of_lt (mem_Ioi.mp ht)) (Real.exp_pos _).le

/-- `∫_0^∞ t e^{-tx} dt = 1/x²` for `x > 0`. -/

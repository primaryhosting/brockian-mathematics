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

lemma tendsto_arctan_half : Tendsto (fun t : ℝ => Real.arctan (t / 2)) atTop (𝓝 (π / 2)) := by
  have h2 : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h2


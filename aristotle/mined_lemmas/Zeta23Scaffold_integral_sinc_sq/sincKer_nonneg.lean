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

lemma sincKer_nonneg {x t : ℝ} (ht : 0 ≤ t) : 0 ≤ sincKer x t := by
  have := Real.exp_pos (-(t * x))
  have : (0:ℝ) ≤ Real.sin x ^ 2 := sq_nonneg _
  unfold sincKer
  positivity

